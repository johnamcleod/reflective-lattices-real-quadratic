import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd24_2_0 : subd24_2 [-2] = true := by decide +kernel
theorem subd24_2_1 : subd24_2 [-1] = true := by decide +kernel
theorem subd24_2_2 : subd24_2 [0, -3] = true := by decide +kernel
theorem subd24_2_3 : subd24_2 [0, -2] = true := by decide +kernel
theorem subd24_2_4 : subd24_2 [0, -1] = true := by decide +kernel
theorem subd24_2_5 : subd24_2 [0, 0] = true := by decide +kernel
theorem subd24_2_6 : subd24_2 [0, 1] = true := by decide +kernel
theorem subd24_2_7 : subd24_2 [0, 2] = true := by decide +kernel
theorem subd24_2_8 : subd24_2 [1] = true := by decide +kernel
theorem subd24_2_9 : subd24_2 [2] = true := by decide +kernel
theorem sbd24_2_0 : ∀ q ∈ blkd24_2_0, subd24_2 q = true := by
  unfold blkd24_2_0
  exact List.forall_mem_cons.2 ⟨subd24_2_0, List.forall_mem_cons.2 ⟨subd24_2_1, List.forall_mem_cons.2 ⟨subd24_2_2, List.forall_mem_cons.2 ⟨subd24_2_3, List.forall_mem_cons.2 ⟨subd24_2_4, List.forall_mem_cons.2 ⟨subd24_2_5, List.forall_mem_cons.2 ⟨subd24_2_6, List.forall_mem_cons.2 ⟨subd24_2_7, List.forall_mem_cons.2 ⟨subd24_2_8, List.forall_mem_cons.2 ⟨subd24_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd24_3 : ldCheck G d24_3.U d24_3.ms ldd24_3 = true := by decide +kernel
theorem pre_okd24_3 : subPre G cell24 d24_3 = true := by decide +kernel
theorem subd24_3_0 : subd24_3 [-2] = true := by decide +kernel
theorem subd24_3_1 : subd24_3 [-1, -3] = true := by decide +kernel
theorem subd24_3_2 : subd24_3 [-1, -2] = true := by decide +kernel
theorem subd24_3_3 : subd24_3 [-1, -1] = true := by decide +kernel
theorem subd24_3_4 : subd24_3 [-1, 0] = true := by decide +kernel
theorem subd24_3_5 : subd24_3 [-1, 1] = true := by decide +kernel
theorem subd24_3_6 : subd24_3 [0, -3] = true := by decide +kernel
theorem subd24_3_7 : subd24_3 [0, -2] = true := by decide +kernel
theorem subd24_3_8 : subd24_3 [0, -1] = true := by decide +kernel
theorem subd24_3_9 : subd24_3 [0, 0] = true := by decide +kernel
theorem subd24_3_10 : subd24_3 [0, 1] = true := by decide +kernel
theorem subd24_3_11 : subd24_3 [0, 2] = true := by decide +kernel
theorem subd24_3_12 : subd24_3 [1, -2] = true := by decide +kernel
theorem subd24_3_13 : subd24_3 [1, -1] = true := by decide +kernel
theorem subd24_3_14 : subd24_3 [1, 0] = true := by decide +kernel
theorem subd24_3_15 : subd24_3 [1, 1] = true := by decide +kernel
theorem subd24_3_16 : subd24_3 [1, 2] = true := by decide +kernel
theorem subd24_3_17 : subd24_3 [2] = true := by decide +kernel
theorem sbd24_3_0 : ∀ q ∈ blkd24_3_0, subd24_3 q = true := by
  unfold blkd24_3_0
  exact List.forall_mem_cons.2 ⟨subd24_3_0, List.forall_mem_cons.2 ⟨subd24_3_1, List.forall_mem_cons.2 ⟨subd24_3_2, List.forall_mem_cons.2 ⟨subd24_3_3, List.forall_mem_cons.2 ⟨subd24_3_4, List.forall_mem_cons.2 ⟨subd24_3_5, List.forall_mem_cons.2 ⟨subd24_3_6, List.forall_mem_cons.2 ⟨subd24_3_7, List.forall_mem_cons.2 ⟨subd24_3_8, List.forall_mem_cons.2 ⟨subd24_3_9, List.forall_mem_cons.2 ⟨subd24_3_10, List.forall_mem_cons.2 ⟨subd24_3_11, List.forall_mem_cons.2 ⟨subd24_3_12, List.forall_mem_cons.2 ⟨subd24_3_13, List.forall_mem_cons.2 ⟨subd24_3_14, List.forall_mem_cons.2 ⟨subd24_3_15, List.forall_mem_cons.2 ⟨subd24_3_16, List.forall_mem_cons.2 ⟨subd24_3_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd25_0 : ldCheck G d25_0.U d25_0.ms ldd25_0 = true := by decide +kernel
theorem pre_okd25_0 : subPre G cell25 d25_0 = true := by decide +kernel
theorem subd25_0_0 : subd25_0 [-2] = true := by decide +kernel
theorem subd25_0_1 : subd25_0 [-1] = true := by decide +kernel
theorem subd25_0_2 : subd25_0 [0, -3] = true := by decide +kernel
theorem subd25_0_3 : subd25_0 [0, -2] = true := by decide +kernel
theorem subd25_0_4 : subd25_0 [0, -1] = true := by decide +kernel
theorem subd25_0_5 : subd25_0 [0, 0] = true := by decide +kernel
theorem subd25_0_6 : subd25_0 [0, 1] = true := by decide +kernel
theorem subd25_0_7 : subd25_0 [0, 2] = true := by decide +kernel
theorem subd25_0_8 : subd25_0 [1] = true := by decide +kernel
theorem subd25_0_9 : subd25_0 [2] = true := by decide +kernel
theorem sbd25_0_0 : ∀ q ∈ blkd25_0_0, subd25_0 q = true := by
  unfold blkd25_0_0
  exact List.forall_mem_cons.2 ⟨subd25_0_0, List.forall_mem_cons.2 ⟨subd25_0_1, List.forall_mem_cons.2 ⟨subd25_0_2, List.forall_mem_cons.2 ⟨subd25_0_3, List.forall_mem_cons.2 ⟨subd25_0_4, List.forall_mem_cons.2 ⟨subd25_0_5, List.forall_mem_cons.2 ⟨subd25_0_6, List.forall_mem_cons.2 ⟨subd25_0_7, List.forall_mem_cons.2 ⟨subd25_0_8, List.forall_mem_cons.2 ⟨subd25_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd25_1 : ldCheck G d25_1.U d25_1.ms ldd25_1 = true := by decide +kernel
theorem pre_okd25_1 : subPre G cell25 d25_1 = true := by decide +kernel
theorem subd25_1_0 : subd25_1 [-1, -2] = true := by decide +kernel
theorem subd25_1_1 : subd25_1 [-1, -1] = true := by decide +kernel
theorem subd25_1_2 : subd25_1 [-1, 0] = true := by decide +kernel
theorem subd25_1_3 : subd25_1 [-1, 1] = true := by decide +kernel
theorem subd25_1_4 : subd25_1 [-1, 2] = true := by decide +kernel
theorem subd25_1_5 : subd25_1 [0, -3] = true := by decide +kernel
theorem subd25_1_6 : subd25_1 [0, -2] = true := by decide +kernel
theorem subd25_1_7 : subd25_1 [0, -1] = true := by decide +kernel
theorem subd25_1_8 : subd25_1 [0, 0] = true := by decide +kernel
theorem subd25_1_9 : subd25_1 [0, 1] = true := by decide +kernel
theorem subd25_1_10 : subd25_1 [0, 2] = true := by decide +kernel
theorem subd25_1_11 : subd25_1 [1, -3] = true := by decide +kernel
theorem subd25_1_12 : subd25_1 [1, -2] = true := by decide +kernel
theorem subd25_1_13 : subd25_1 [1, -1] = true := by decide +kernel
theorem subd25_1_14 : subd25_1 [1, 0] = true := by decide +kernel
theorem subd25_1_15 : subd25_1 [1, 1] = true := by decide +kernel
theorem sbd25_1_0 : ∀ q ∈ blkd25_1_0, subd25_1 q = true := by
  unfold blkd25_1_0
  exact List.forall_mem_cons.2 ⟨subd25_1_0, List.forall_mem_cons.2 ⟨subd25_1_1, List.forall_mem_cons.2 ⟨subd25_1_2, List.forall_mem_cons.2 ⟨subd25_1_3, List.forall_mem_cons.2 ⟨subd25_1_4, List.forall_mem_cons.2 ⟨subd25_1_5, List.forall_mem_cons.2 ⟨subd25_1_6, List.forall_mem_cons.2 ⟨subd25_1_7, List.forall_mem_cons.2 ⟨subd25_1_8, List.forall_mem_cons.2 ⟨subd25_1_9, List.forall_mem_cons.2 ⟨subd25_1_10, List.forall_mem_cons.2 ⟨subd25_1_11, List.forall_mem_cons.2 ⟨subd25_1_12, List.forall_mem_cons.2 ⟨subd25_1_13, List.forall_mem_cons.2 ⟨subd25_1_14, List.forall_mem_cons.2 ⟨subd25_1_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd25_2 : ldCheck G d25_2.U d25_2.ms ldd25_2 = true := by decide +kernel
theorem pre_okd25_2 : subPre G cell25 d25_2 = true := by decide +kernel
theorem subd25_2_0 : subd25_2 [-3] = true := by decide +kernel
theorem subd25_2_1 : subd25_2 [-2] = true := by decide +kernel
theorem subd25_2_2 : subd25_2 [-1] = true := by decide +kernel
theorem subd25_2_3 : subd25_2 [0, -3] = true := by decide +kernel
theorem subd25_2_4 : subd25_2 [0, -2] = true := by decide +kernel
theorem subd25_2_5 : subd25_2 [0, -1] = true := by decide +kernel
theorem subd25_2_6 : subd25_2 [0, 0] = true := by decide +kernel
theorem subd25_2_7 : subd25_2 [0, 1] = true := by decide +kernel
theorem subd25_2_8 : subd25_2 [0, 2] = true := by decide +kernel
theorem subd25_2_9 : subd25_2 [1] = true := by decide +kernel
theorem subd25_2_10 : subd25_2 [2] = true := by decide +kernel
theorem subd25_2_11 : subd25_2 [3] = true := by decide +kernel
theorem sbd25_2_0 : ∀ q ∈ blkd25_2_0, subd25_2 q = true := by
  unfold blkd25_2_0
  exact List.forall_mem_cons.2 ⟨subd25_2_0, List.forall_mem_cons.2 ⟨subd25_2_1, List.forall_mem_cons.2 ⟨subd25_2_2, List.forall_mem_cons.2 ⟨subd25_2_3, List.forall_mem_cons.2 ⟨subd25_2_4, List.forall_mem_cons.2 ⟨subd25_2_5, List.forall_mem_cons.2 ⟨subd25_2_6, List.forall_mem_cons.2 ⟨subd25_2_7, List.forall_mem_cons.2 ⟨subd25_2_8, List.forall_mem_cons.2 ⟨subd25_2_9, List.forall_mem_cons.2 ⟨subd25_2_10, List.forall_mem_cons.2 ⟨subd25_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd25_3 : ldCheck G d25_3.U d25_3.ms ldd25_3 = true := by decide +kernel
theorem pre_okd25_3 : subPre G cell25 d25_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
