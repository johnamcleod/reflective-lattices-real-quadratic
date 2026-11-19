import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_nil _⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_nil _⟩
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
theorem ld_okd13_6 : ldCheck G d13_6.U d13_6.ms ldd13_6 = true := by decide +kernel
theorem pre_okd13_6 : subPre G cell13 d13_6 = true := by decide +kernel
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
theorem subd13_7_0 : subd13_7 [-1] = true := by decide +kernel
theorem subd13_7_1 : subd13_7 [0] = true := by decide +kernel
theorem subd13_7_2 : subd13_7 [1] = true := by decide +kernel
theorem sbd13_7_0 : ∀ q ∈ blkd13_7_0, subd13_7 q = true := by
  unfold blkd13_7_0
  exact List.forall_mem_cons.2 ⟨subd13_7_0, List.forall_mem_cons.2 ⟨subd13_7_1, List.forall_mem_cons.2 ⟨subd13_7_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
