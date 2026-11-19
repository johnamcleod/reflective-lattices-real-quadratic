import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_6_0 : subd13_6 [-2] = true := by decide +kernel
theorem subd13_6_1 : subd13_6 [-1, -3] = true := by decide +kernel
theorem subd13_6_2 : subd13_6 [-1, -2] = true := by decide +kernel
theorem subd13_6_3 : subd13_6 [-1, -1] = true := by decide +kernel
theorem subd13_6_4 : subd13_6 [-1, 0] = true := by decide +kernel
theorem subd13_6_5 : subd13_6 [-1, 1] = true := by decide +kernel
theorem subd13_6_6 : subd13_6 [0, -3] = true := by decide +kernel
theorem subd13_6_7 : subd13_6 [0, -2] = true := by decide +kernel
theorem subd13_6_8 : subd13_6 [0, -1] = true := by decide +kernel
theorem subd13_6_9 : subd13_6 [0, 0] = true := by decide +kernel
theorem subd13_6_10 : subd13_6 [0, 1] = true := by decide +kernel
theorem subd13_6_11 : subd13_6 [0, 2] = true := by decide +kernel
theorem subd13_6_12 : subd13_6 [1, -2] = true := by decide +kernel
theorem subd13_6_13 : subd13_6 [1, -1] = true := by decide +kernel
theorem subd13_6_14 : subd13_6 [1, 0] = true := by decide +kernel
theorem subd13_6_15 : subd13_6 [1, 1] = true := by decide +kernel
theorem subd13_6_16 : subd13_6 [1, 2] = true := by decide +kernel
theorem subd13_6_17 : subd13_6 [2] = true := by decide +kernel
theorem sbd13_6_0 : ∀ q ∈ blkd13_6_0, subd13_6 q = true := by
  unfold blkd13_6_0
  exact List.forall_mem_cons.2 ⟨subd13_6_0, List.forall_mem_cons.2 ⟨subd13_6_1, List.forall_mem_cons.2 ⟨subd13_6_2, List.forall_mem_cons.2 ⟨subd13_6_3, List.forall_mem_cons.2 ⟨subd13_6_4, List.forall_mem_cons.2 ⟨subd13_6_5, List.forall_mem_cons.2 ⟨subd13_6_6, List.forall_mem_cons.2 ⟨subd13_6_7, List.forall_mem_cons.2 ⟨subd13_6_8, List.forall_mem_cons.2 ⟨subd13_6_9, List.forall_mem_cons.2 ⟨subd13_6_10, List.forall_mem_cons.2 ⟨subd13_6_11, List.forall_mem_cons.2 ⟨subd13_6_12, List.forall_mem_cons.2 ⟨subd13_6_13, List.forall_mem_cons.2 ⟨subd13_6_14, List.forall_mem_cons.2 ⟨subd13_6_15, List.forall_mem_cons.2 ⟨subd13_6_16, List.forall_mem_cons.2 ⟨subd13_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_7 : ldCheck G d13_7.U d13_7.ms ldd13_7 = true := by decide +kernel
theorem pre_okd13_7 : subPre G cell13 d13_7 = true := by decide +kernel
theorem subd13_7_0 : subd13_7 [-2] = true := by decide +kernel
theorem subd13_7_1 : subd13_7 [-1, -3] = true := by decide +kernel
theorem subd13_7_2 : subd13_7 [-1, -2] = true := by decide +kernel
theorem subd13_7_3 : subd13_7 [-1, -1] = true := by decide +kernel
theorem subd13_7_4 : subd13_7 [-1, 0] = true := by decide +kernel
theorem subd13_7_5 : subd13_7 [-1, 1] = true := by decide +kernel
theorem subd13_7_6 : subd13_7 [-1, 2] = true := by decide +kernel
theorem subd13_7_7 : subd13_7 [0, -3] = true := by decide +kernel
theorem subd13_7_8 : subd13_7 [0, -2] = true := by decide +kernel
theorem subd13_7_9 : subd13_7 [0, -1] = true := by decide +kernel
theorem subd13_7_10 : subd13_7 [0, 0] = true := by decide +kernel
theorem subd13_7_11 : subd13_7 [0, 1] = true := by decide +kernel
theorem subd13_7_12 : subd13_7 [0, 2] = true := by decide +kernel
theorem subd13_7_13 : subd13_7 [1, -3] = true := by decide +kernel
theorem subd13_7_14 : subd13_7 [1, -2] = true := by decide +kernel
theorem subd13_7_15 : subd13_7 [1, -1] = true := by decide +kernel
theorem subd13_7_16 : subd13_7 [1, 0] = true := by decide +kernel
theorem subd13_7_17 : subd13_7 [1, 1] = true := by decide +kernel
theorem subd13_7_18 : subd13_7 [1, 2] = true := by decide +kernel
theorem subd13_7_19 : subd13_7 [2] = true := by decide +kernel
theorem sbd13_7_0 : ∀ q ∈ blkd13_7_0, subd13_7 q = true := by
  unfold blkd13_7_0
  exact List.forall_mem_cons.2 ⟨subd13_7_0, List.forall_mem_cons.2 ⟨subd13_7_1, List.forall_mem_cons.2 ⟨subd13_7_2, List.forall_mem_cons.2 ⟨subd13_7_3, List.forall_mem_cons.2 ⟨subd13_7_4, List.forall_mem_cons.2 ⟨subd13_7_5, List.forall_mem_cons.2 ⟨subd13_7_6, List.forall_mem_cons.2 ⟨subd13_7_7, List.forall_mem_cons.2 ⟨subd13_7_8, List.forall_mem_cons.2 ⟨subd13_7_9, List.forall_mem_cons.2 ⟨subd13_7_10, List.forall_mem_cons.2 ⟨subd13_7_11, List.forall_mem_cons.2 ⟨subd13_7_12, List.forall_mem_cons.2 ⟨subd13_7_13, List.forall_mem_cons.2 ⟨subd13_7_14, List.forall_mem_cons.2 ⟨subd13_7_15, List.forall_mem_cons.2 ⟨subd13_7_16, List.forall_mem_cons.2 ⟨subd13_7_17, List.forall_mem_cons.2 ⟨subd13_7_18, List.forall_mem_cons.2 ⟨subd13_7_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-2] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-1] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [0, -3] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [0, -2] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [0, -1] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [0, 0] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [0, 1] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [0, 2] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [1] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [2] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-3] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-2, -2] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-2, -1] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-2, 0] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-2, 1] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-2, 2] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-1, -3] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-1, -1] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-1, 0] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-1, 1] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-1, 2] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [0, -1] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [1, -3] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [1, -2] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [1, -1] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [1, 0] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [1, 1] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [1, 2] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [2, -3] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [2, -2] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [2, -1] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [2, 0] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [2, 1] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [3] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
