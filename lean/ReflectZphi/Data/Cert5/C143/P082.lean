import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd23_0_0 : subd23_0 [-1] = true := by decide +kernel
theorem subd23_0_1 : subd23_0 [0, -2] = true := by decide +kernel
theorem subd23_0_2 : subd23_0 [0, -1] = true := by decide +kernel
theorem subd23_0_3 : subd23_0 [0, 0] = true := by decide +kernel
theorem subd23_0_4 : subd23_0 [0, 1] = true := by decide +kernel
theorem subd23_0_5 : subd23_0 [1] = true := by decide +kernel
theorem sbd23_0_0 : ∀ q ∈ blkd23_0_0, subd23_0 q = true := by
  unfold blkd23_0_0
  exact List.forall_mem_cons.2 ⟨subd23_0_0, List.forall_mem_cons.2 ⟨subd23_0_1, List.forall_mem_cons.2 ⟨subd23_0_2, List.forall_mem_cons.2 ⟨subd23_0_3, List.forall_mem_cons.2 ⟨subd23_0_4, List.forall_mem_cons.2 ⟨subd23_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd23_1 : ldCheck G d23_1.U d23_1.ms ldd23_1 = true := by decide +kernel
theorem pre_okd23_1 : subPre G cell23 d23_1 = true := by decide +kernel
theorem subd23_1_0 : subd23_1 [-1] = true := by decide +kernel
theorem subd23_1_1 : subd23_1 [0, -2] = true := by decide +kernel
theorem subd23_1_2 : subd23_1 [0, -1] = true := by decide +kernel
theorem subd23_1_3 : subd23_1 [0, 0, -9] = true := by decide +kernel
theorem subd23_1_4 : subd23_1 [0, 0, -8] = true := by decide +kernel
theorem subd23_1_5 : subd23_1 [0, 0, -7] = true := by decide +kernel
theorem subd23_1_6 : subd23_1 [0, 0, -6] = true := by decide +kernel
theorem subd23_1_7 : subd23_1 [0, 0, -5] = true := by decide +kernel
theorem subd23_1_8 : subd23_1 [0, 0, -4] = true := by decide +kernel
theorem subd23_1_9 : subd23_1 [0, 0, -3] = true := by decide +kernel
theorem subd23_1_10 : subd23_1 [0, 0, -2] = true := by decide +kernel
theorem subd23_1_11 : subd23_1 [0, 0, -1] = true := by decide +kernel
theorem subd23_1_12 : subd23_1 [0, 0, 0] = true := by decide +kernel
theorem subd23_1_13 : subd23_1 [0, 0, 1] = true := by decide +kernel
theorem subd23_1_14 : subd23_1 [0, 0, 2] = true := by decide +kernel
theorem subd23_1_15 : subd23_1 [0, 0, 3] = true := by decide +kernel
theorem subd23_1_16 : subd23_1 [0, 0, 4] = true := by decide +kernel
theorem subd23_1_17 : subd23_1 [0, 0, 5] = true := by decide +kernel
theorem subd23_1_18 : subd23_1 [0, 0, 6] = true := by decide +kernel
theorem subd23_1_19 : subd23_1 [0, 0, 7] = true := by decide +kernel
theorem subd23_1_20 : subd23_1 [0, 0, 8] = true := by decide +kernel
theorem subd23_1_21 : subd23_1 [0, 1] = true := by decide +kernel
theorem subd23_1_22 : subd23_1 [1] = true := by decide +kernel
theorem sbd23_1_0 : ∀ q ∈ blkd23_1_0, subd23_1 q = true := by
  unfold blkd23_1_0
  exact List.forall_mem_cons.2 ⟨subd23_1_0, List.forall_mem_cons.2 ⟨subd23_1_1, List.forall_mem_cons.2 ⟨subd23_1_2, List.forall_mem_cons.2 ⟨subd23_1_3, List.forall_mem_cons.2 ⟨subd23_1_4, List.forall_mem_cons.2 ⟨subd23_1_5, List.forall_mem_cons.2 ⟨subd23_1_6, List.forall_mem_cons.2 ⟨subd23_1_7, List.forall_mem_cons.2 ⟨subd23_1_8, List.forall_mem_cons.2 ⟨subd23_1_9, List.forall_mem_cons.2 ⟨subd23_1_10, List.forall_mem_cons.2 ⟨subd23_1_11, List.forall_mem_cons.2 ⟨subd23_1_12, List.forall_mem_cons.2 ⟨subd23_1_13, List.forall_mem_cons.2 ⟨subd23_1_14, List.forall_mem_cons.2 ⟨subd23_1_15, List.forall_mem_cons.2 ⟨subd23_1_16, List.forall_mem_cons.2 ⟨subd23_1_17, List.forall_mem_cons.2 ⟨subd23_1_18, List.forall_mem_cons.2 ⟨subd23_1_19, List.forall_mem_cons.2 ⟨subd23_1_20, List.forall_mem_cons.2 ⟨subd23_1_21, List.forall_mem_cons.2 ⟨subd23_1_22, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd23_2 : ldCheck G d23_2.U d23_2.ms ldd23_2 = true := by decide +kernel
theorem pre_okd23_2 : subPre G cell23 d23_2 = true := by decide +kernel
theorem subd23_2_0 : subd23_2 [-3] = true := by decide +kernel
theorem subd23_2_1 : subd23_2 [-2] = true := by decide +kernel
theorem subd23_2_2 : subd23_2 [-1] = true := by decide +kernel
theorem subd23_2_3 : subd23_2 [0] = true := by decide +kernel
theorem subd23_2_4 : subd23_2 [1] = true := by decide +kernel
theorem subd23_2_5 : subd23_2 [2] = true := by decide +kernel
theorem subd23_2_6 : subd23_2 [3] = true := by decide +kernel
theorem sbd23_2_0 : ∀ q ∈ blkd23_2_0, subd23_2 q = true := by
  unfold blkd23_2_0
  exact List.forall_mem_cons.2 ⟨subd23_2_0, List.forall_mem_cons.2 ⟨subd23_2_1, List.forall_mem_cons.2 ⟨subd23_2_2, List.forall_mem_cons.2 ⟨subd23_2_3, List.forall_mem_cons.2 ⟨subd23_2_4, List.forall_mem_cons.2 ⟨subd23_2_5, List.forall_mem_cons.2 ⟨subd23_2_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd23_3 : ldCheck G d23_3.U d23_3.ms ldd23_3 = true := by decide +kernel
theorem pre_okd23_3 : subPre G cell23 d23_3 = true := by decide +kernel
theorem subd23_3_0 : subd23_3 [-1] = true := by decide +kernel
theorem subd23_3_1 : subd23_3 [0, -2] = true := by decide +kernel
theorem subd23_3_2 : subd23_3 [0, -1] = true := by decide +kernel
theorem subd23_3_3 : subd23_3 [0, 0] = true := by decide +kernel
theorem subd23_3_4 : subd23_3 [0, 1] = true := by decide +kernel
theorem subd23_3_5 : subd23_3 [1] = true := by decide +kernel
theorem sbd23_3_0 : ∀ q ∈ blkd23_3_0, subd23_3 q = true := by
  unfold blkd23_3_0
  exact List.forall_mem_cons.2 ⟨subd23_3_0, List.forall_mem_cons.2 ⟨subd23_3_1, List.forall_mem_cons.2 ⟨subd23_3_2, List.forall_mem_cons.2 ⟨subd23_3_3, List.forall_mem_cons.2 ⟨subd23_3_4, List.forall_mem_cons.2 ⟨subd23_3_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd24_0 : ldCheck G d24_0.U d24_0.ms ldd24_0 = true := by decide +kernel
theorem pre_okd24_0 : subPre G cell24 d24_0 = true := by decide +kernel
theorem subd24_0_0 : subd24_0 [-2] = true := by decide +kernel
theorem subd24_0_1 : subd24_0 [-1] = true := by decide +kernel
theorem subd24_0_2 : subd24_0 [0, -3] = true := by decide +kernel
theorem subd24_0_3 : subd24_0 [0, -2] = true := by decide +kernel
theorem subd24_0_4 : subd24_0 [0, -1] = true := by decide +kernel
theorem subd24_0_5 : subd24_0 [0, 0] = true := by decide +kernel
theorem subd24_0_6 : subd24_0 [0, 1] = true := by decide +kernel
theorem subd24_0_7 : subd24_0 [0, 2] = true := by decide +kernel
theorem subd24_0_8 : subd24_0 [1] = true := by decide +kernel
theorem subd24_0_9 : subd24_0 [2] = true := by decide +kernel
theorem sbd24_0_0 : ∀ q ∈ blkd24_0_0, subd24_0 q = true := by
  unfold blkd24_0_0
  exact List.forall_mem_cons.2 ⟨subd24_0_0, List.forall_mem_cons.2 ⟨subd24_0_1, List.forall_mem_cons.2 ⟨subd24_0_2, List.forall_mem_cons.2 ⟨subd24_0_3, List.forall_mem_cons.2 ⟨subd24_0_4, List.forall_mem_cons.2 ⟨subd24_0_5, List.forall_mem_cons.2 ⟨subd24_0_6, List.forall_mem_cons.2 ⟨subd24_0_7, List.forall_mem_cons.2 ⟨subd24_0_8, List.forall_mem_cons.2 ⟨subd24_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd24_1 : ldCheck G d24_1.U d24_1.ms ldd24_1 = true := by decide +kernel
theorem pre_okd24_1 : subPre G cell24 d24_1 = true := by decide +kernel
theorem subd24_1_0 : subd24_1 [-1] = true := by decide +kernel
theorem subd24_1_1 : subd24_1 [0, -2] = true := by decide +kernel
theorem subd24_1_2 : subd24_1 [0, -1] = true := by decide +kernel
theorem subd24_1_3 : subd24_1 [0, 0, -8] = true := by decide +kernel
theorem subd24_1_4 : subd24_1 [0, 0, -7] = true := by decide +kernel
theorem subd24_1_5 : subd24_1 [0, 0, -6] = true := by decide +kernel
theorem subd24_1_6 : subd24_1 [0, 0, -5] = true := by decide +kernel
theorem subd24_1_7 : subd24_1 [0, 0, -4] = true := by decide +kernel
theorem subd24_1_8 : subd24_1 [0, 0, -3] = true := by decide +kernel
theorem subd24_1_9 : subd24_1 [0, 0, -2] = true := by decide +kernel
theorem subd24_1_10 : subd24_1 [0, 0, -1] = true := by decide +kernel
theorem subd24_1_11 : subd24_1 [0, 0, 0] = true := by decide +kernel
theorem subd24_1_12 : subd24_1 [0, 0, 1] = true := by decide +kernel
theorem subd24_1_13 : subd24_1 [0, 0, 2] = true := by decide +kernel
theorem subd24_1_14 : subd24_1 [0, 0, 3] = true := by decide +kernel
theorem subd24_1_15 : subd24_1 [0, 0, 4] = true := by decide +kernel
theorem subd24_1_16 : subd24_1 [0, 0, 5] = true := by decide +kernel
theorem subd24_1_17 : subd24_1 [0, 0, 6] = true := by decide +kernel
theorem subd24_1_18 : subd24_1 [0, 0, 7] = true := by decide +kernel
theorem subd24_1_19 : subd24_1 [0, 1] = true := by decide +kernel
theorem subd24_1_20 : subd24_1 [1] = true := by decide +kernel
theorem sbd24_1_0 : ∀ q ∈ blkd24_1_0, subd24_1 q = true := by
  unfold blkd24_1_0
  exact List.forall_mem_cons.2 ⟨subd24_1_0, List.forall_mem_cons.2 ⟨subd24_1_1, List.forall_mem_cons.2 ⟨subd24_1_2, List.forall_mem_cons.2 ⟨subd24_1_3, List.forall_mem_cons.2 ⟨subd24_1_4, List.forall_mem_cons.2 ⟨subd24_1_5, List.forall_mem_cons.2 ⟨subd24_1_6, List.forall_mem_cons.2 ⟨subd24_1_7, List.forall_mem_cons.2 ⟨subd24_1_8, List.forall_mem_cons.2 ⟨subd24_1_9, List.forall_mem_cons.2 ⟨subd24_1_10, List.forall_mem_cons.2 ⟨subd24_1_11, List.forall_mem_cons.2 ⟨subd24_1_12, List.forall_mem_cons.2 ⟨subd24_1_13, List.forall_mem_cons.2 ⟨subd24_1_14, List.forall_mem_cons.2 ⟨subd24_1_15, List.forall_mem_cons.2 ⟨subd24_1_16, List.forall_mem_cons.2 ⟨subd24_1_17, List.forall_mem_cons.2 ⟨subd24_1_18, List.forall_mem_cons.2 ⟨subd24_1_19, List.forall_mem_cons.2 ⟨subd24_1_20, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd24_2 : ldCheck G d24_2.U d24_2.ms ldd24_2 = true := by decide +kernel
theorem pre_okd24_2 : subPre G cell24 d24_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
