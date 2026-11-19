import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_7_0 : subd13_7 [-3] = true := by decide +kernel
theorem subd13_7_1 : subd13_7 [-2] = true := by decide +kernel
theorem subd13_7_2 : subd13_7 [-1] = true := by decide +kernel
theorem subd13_7_3 : subd13_7 [0, -4] = true := by decide +kernel
theorem subd13_7_4 : subd13_7 [0, -3] = true := by decide +kernel
theorem subd13_7_5 : subd13_7 [0, -2] = true := by decide +kernel
theorem subd13_7_6 : subd13_7 [0, -1] = true := by decide +kernel
theorem subd13_7_7 : subd13_7 [0, 0] = true := by decide +kernel
theorem subd13_7_8 : subd13_7 [0, 1] = true := by decide +kernel
theorem subd13_7_9 : subd13_7 [0, 2] = true := by decide +kernel
theorem subd13_7_10 : subd13_7 [0, 3] = true := by decide +kernel
theorem subd13_7_11 : subd13_7 [1] = true := by decide +kernel
theorem subd13_7_12 : subd13_7 [2] = true := by decide +kernel
theorem subd13_7_13 : subd13_7 [3] = true := by decide +kernel
theorem sbd13_7_0 : ∀ q ∈ blkd13_7_0, subd13_7 q = true := by
  unfold blkd13_7_0
  exact List.forall_mem_cons.2 ⟨subd13_7_0, List.forall_mem_cons.2 ⟨subd13_7_1, List.forall_mem_cons.2 ⟨subd13_7_2, List.forall_mem_cons.2 ⟨subd13_7_3, List.forall_mem_cons.2 ⟨subd13_7_4, List.forall_mem_cons.2 ⟨subd13_7_5, List.forall_mem_cons.2 ⟨subd13_7_6, List.forall_mem_cons.2 ⟨subd13_7_7, List.forall_mem_cons.2 ⟨subd13_7_8, List.forall_mem_cons.2 ⟨subd13_7_9, List.forall_mem_cons.2 ⟨subd13_7_10, List.forall_mem_cons.2 ⟨subd13_7_11, List.forall_mem_cons.2 ⟨subd13_7_12, List.forall_mem_cons.2 ⟨subd13_7_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_8 : ldCheck G d13_8.U d13_8.ms ldd13_8 = true := by decide +kernel
theorem pre_okd13_8 : subPre G cell13 d13_8 = true := by decide +kernel
theorem subd13_8_0 : subd13_8 [-2] = true := by decide +kernel
theorem subd13_8_1 : subd13_8 [-1, -3] = true := by decide +kernel
theorem subd13_8_2 : subd13_8 [-1, -2] = true := by decide +kernel
theorem subd13_8_3 : subd13_8 [-1, -1] = true := by decide +kernel
theorem subd13_8_4 : subd13_8 [-1, 0] = true := by decide +kernel
theorem subd13_8_5 : subd13_8 [-1, 1] = true := by decide +kernel
theorem subd13_8_6 : subd13_8 [0, -3] = true := by decide +kernel
theorem subd13_8_7 : subd13_8 [0, -2] = true := by decide +kernel
theorem subd13_8_8 : subd13_8 [0, -1] = true := by decide +kernel
theorem subd13_8_9 : subd13_8 [0, 0] = true := by decide +kernel
theorem subd13_8_10 : subd13_8 [0, 1] = true := by decide +kernel
theorem subd13_8_11 : subd13_8 [0, 2] = true := by decide +kernel
theorem subd13_8_12 : subd13_8 [1, -2] = true := by decide +kernel
theorem subd13_8_13 : subd13_8 [1, -1] = true := by decide +kernel
theorem subd13_8_14 : subd13_8 [1, 0] = true := by decide +kernel
theorem subd13_8_15 : subd13_8 [1, 1] = true := by decide +kernel
theorem subd13_8_16 : subd13_8 [1, 2] = true := by decide +kernel
theorem subd13_8_17 : subd13_8 [2] = true := by decide +kernel
theorem sbd13_8_0 : ∀ q ∈ blkd13_8_0, subd13_8 q = true := by
  unfold blkd13_8_0
  exact List.forall_mem_cons.2 ⟨subd13_8_0, List.forall_mem_cons.2 ⟨subd13_8_1, List.forall_mem_cons.2 ⟨subd13_8_2, List.forall_mem_cons.2 ⟨subd13_8_3, List.forall_mem_cons.2 ⟨subd13_8_4, List.forall_mem_cons.2 ⟨subd13_8_5, List.forall_mem_cons.2 ⟨subd13_8_6, List.forall_mem_cons.2 ⟨subd13_8_7, List.forall_mem_cons.2 ⟨subd13_8_8, List.forall_mem_cons.2 ⟨subd13_8_9, List.forall_mem_cons.2 ⟨subd13_8_10, List.forall_mem_cons.2 ⟨subd13_8_11, List.forall_mem_cons.2 ⟨subd13_8_12, List.forall_mem_cons.2 ⟨subd13_8_13, List.forall_mem_cons.2 ⟨subd13_8_14, List.forall_mem_cons.2 ⟨subd13_8_15, List.forall_mem_cons.2 ⟨subd13_8_16, List.forall_mem_cons.2 ⟨subd13_8_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_9 : ldCheck G d13_9.U d13_9.ms ldd13_9 = true := by decide +kernel
theorem pre_okd13_9 : subPre G cell13 d13_9 = true := by decide +kernel
theorem subd13_9_0 : subd13_9 [-2] = true := by decide +kernel
theorem subd13_9_1 : subd13_9 [-1, -4] = true := by decide +kernel
theorem subd13_9_2 : subd13_9 [-1, -3] = true := by decide +kernel
theorem subd13_9_3 : subd13_9 [-1, -2] = true := by decide +kernel
theorem subd13_9_4 : subd13_9 [-1, -1] = true := by decide +kernel
theorem subd13_9_5 : subd13_9 [-1, 0] = true := by decide +kernel
theorem subd13_9_6 : subd13_9 [-1, 1] = true := by decide +kernel
theorem subd13_9_7 : subd13_9 [-1, 2] = true := by decide +kernel
theorem subd13_9_8 : subd13_9 [0, -4] = true := by decide +kernel
theorem subd13_9_9 : subd13_9 [0, -3] = true := by decide +kernel
theorem subd13_9_10 : subd13_9 [0, -2] = true := by decide +kernel
theorem subd13_9_11 : subd13_9 [0, -1] = true := by decide +kernel
theorem subd13_9_12 : subd13_9 [0, 0] = true := by decide +kernel
theorem subd13_9_13 : subd13_9 [0, 1] = true := by decide +kernel
theorem subd13_9_14 : subd13_9 [0, 2] = true := by decide +kernel
theorem subd13_9_15 : subd13_9 [0, 3] = true := by decide +kernel
theorem subd13_9_16 : subd13_9 [1, -3] = true := by decide +kernel
theorem subd13_9_17 : subd13_9 [1, -2] = true := by decide +kernel
theorem subd13_9_18 : subd13_9 [1, -1] = true := by decide +kernel
theorem subd13_9_19 : subd13_9 [1, 0] = true := by decide +kernel
theorem subd13_9_20 : subd13_9 [1, 1] = true := by decide +kernel
theorem subd13_9_21 : subd13_9 [1, 2] = true := by decide +kernel
theorem subd13_9_22 : subd13_9 [1, 3] = true := by decide +kernel
theorem subd13_9_23 : subd13_9 [2] = true := by decide +kernel
theorem sbd13_9_0 : ∀ q ∈ blkd13_9_0, subd13_9 q = true := by
  unfold blkd13_9_0
  exact List.forall_mem_cons.2 ⟨subd13_9_0, List.forall_mem_cons.2 ⟨subd13_9_1, List.forall_mem_cons.2 ⟨subd13_9_2, List.forall_mem_cons.2 ⟨subd13_9_3, List.forall_mem_cons.2 ⟨subd13_9_4, List.forall_mem_cons.2 ⟨subd13_9_5, List.forall_mem_cons.2 ⟨subd13_9_6, List.forall_mem_cons.2 ⟨subd13_9_7, List.forall_mem_cons.2 ⟨subd13_9_8, List.forall_mem_cons.2 ⟨subd13_9_9, List.forall_mem_cons.2 ⟨subd13_9_10, List.forall_mem_cons.2 ⟨subd13_9_11, List.forall_mem_cons.2 ⟨subd13_9_12, List.forall_mem_cons.2 ⟨subd13_9_13, List.forall_mem_cons.2 ⟨subd13_9_14, List.forall_mem_cons.2 ⟨subd13_9_15, List.forall_mem_cons.2 ⟨subd13_9_16, List.forall_mem_cons.2 ⟨subd13_9_17, List.forall_mem_cons.2 ⟨subd13_9_18, List.forall_mem_cons.2 ⟨subd13_9_19, List.forall_mem_cons.2 ⟨subd13_9_20, List.forall_mem_cons.2 ⟨subd13_9_21, List.forall_mem_cons.2 ⟨subd13_9_22, List.forall_mem_cons.2 ⟨subd13_9_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_10 : ldCheck G d13_10.U d13_10.ms ldd13_10 = true := by decide +kernel
theorem pre_okd13_10 : subPre G cell13 d13_10 = true := by decide +kernel
theorem subd13_10_0 : subd13_10 [-1] = true := by decide +kernel
theorem subd13_10_1 : subd13_10 [0, -2] = true := by decide +kernel
theorem subd13_10_2 : subd13_10 [0, -1] = true := by decide +kernel
theorem subd13_10_3 : subd13_10 [0, 0] = true := by decide +kernel
theorem subd13_10_4 : subd13_10 [0, 1] = true := by decide +kernel
theorem subd13_10_5 : subd13_10 [1] = true := by decide +kernel
theorem sbd13_10_0 : ∀ q ∈ blkd13_10_0, subd13_10 q = true := by
  unfold blkd13_10_0
  exact List.forall_mem_cons.2 ⟨subd13_10_0, List.forall_mem_cons.2 ⟨subd13_10_1, List.forall_mem_cons.2 ⟨subd13_10_2, List.forall_mem_cons.2 ⟨subd13_10_3, List.forall_mem_cons.2 ⟨subd13_10_4, List.forall_mem_cons.2 ⟨subd13_10_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_11 : ldCheck G d13_11.U d13_11.ms ldd13_11 = true := by decide +kernel
theorem pre_okd13_11 : subPre G cell13 d13_11 = true := by decide +kernel
theorem subd13_11_0 : subd13_11 [-2] = true := by decide +kernel
theorem subd13_11_1 : subd13_11 [-1] = true := by decide +kernel
theorem subd13_11_2 : subd13_11 [0, -3] = true := by decide +kernel
theorem subd13_11_3 : subd13_11 [0, -2] = true := by decide +kernel
theorem subd13_11_4 : subd13_11 [0, -1] = true := by decide +kernel
theorem subd13_11_5 : subd13_11 [0, 0] = true := by decide +kernel
theorem subd13_11_6 : subd13_11 [0, 1] = true := by decide +kernel
theorem subd13_11_7 : subd13_11 [0, 2] = true := by decide +kernel
theorem subd13_11_8 : subd13_11 [1] = true := by decide +kernel
theorem subd13_11_9 : subd13_11 [2] = true := by decide +kernel
theorem sbd13_11_0 : ∀ q ∈ blkd13_11_0, subd13_11 q = true := by
  unfold blkd13_11_0
  exact List.forall_mem_cons.2 ⟨subd13_11_0, List.forall_mem_cons.2 ⟨subd13_11_1, List.forall_mem_cons.2 ⟨subd13_11_2, List.forall_mem_cons.2 ⟨subd13_11_3, List.forall_mem_cons.2 ⟨subd13_11_4, List.forall_mem_cons.2 ⟨subd13_11_5, List.forall_mem_cons.2 ⟨subd13_11_6, List.forall_mem_cons.2 ⟨subd13_11_7, List.forall_mem_cons.2 ⟨subd13_11_8, List.forall_mem_cons.2 ⟨subd13_11_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_12 : ldCheck G d13_12.U d13_12.ms ldd13_12 = true := by decide +kernel
theorem pre_okd13_12 : subPre G cell13 d13_12 = true := by decide +kernel
theorem subd13_12_0 : subd13_12 [-1] = true := by decide +kernel
theorem subd13_12_1 : subd13_12 [0] = true := by decide +kernel
theorem subd13_12_2 : subd13_12 [1] = true := by decide +kernel
theorem sbd13_12_0 : ∀ q ∈ blkd13_12_0, subd13_12 q = true := by
  unfold blkd13_12_0
  exact List.forall_mem_cons.2 ⟨subd13_12_0, List.forall_mem_cons.2 ⟨subd13_12_1, List.forall_mem_cons.2 ⟨subd13_12_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
