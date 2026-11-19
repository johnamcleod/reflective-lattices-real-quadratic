import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_nil _⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_nil _⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-2] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-1, -2] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-1, -1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-1, 0] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-1, 1] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-1, 2] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [0, -3] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [0, -2] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [0, -1] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [0, 0] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [0, 1] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [0, 2] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [1, -3] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [1, -2] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [1, -1] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [1, 0] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [1, 1] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [1, 2] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [2] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1, -4] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-1, -3] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [0, -4] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [0, 1] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [0, 3] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [1, 2] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [1, 3] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_8 : ldCheck G d5_8.U d5_8.ms ldd5_8 = true := by decide +kernel
theorem pre_okd5_8 : subPre G cell5 d5_8 = true := by decide +kernel
theorem subd5_8_0 : subd5_8 [-3] = true := by decide +kernel
theorem subd5_8_1 : subd5_8 [-2] = true := by decide +kernel
theorem subd5_8_2 : subd5_8 [-1, -4] = true := by decide +kernel
theorem subd5_8_3 : subd5_8 [-1, -3] = true := by decide +kernel
theorem subd5_8_4 : subd5_8 [-1, -2] = true := by decide +kernel
theorem subd5_8_5 : subd5_8 [-1, -1] = true := by decide +kernel
theorem subd5_8_6 : subd5_8 [-1, 0] = true := by decide +kernel
theorem subd5_8_7 : subd5_8 [-1, 1] = true := by decide +kernel
theorem subd5_8_8 : subd5_8 [-1, 2] = true := by decide +kernel
theorem subd5_8_9 : subd5_8 [0, -4] = true := by decide +kernel
theorem subd5_8_10 : subd5_8 [0, -3] = true := by decide +kernel
theorem subd5_8_11 : subd5_8 [0, -2] = true := by decide +kernel
theorem subd5_8_12 : subd5_8 [0, -1] = true := by decide +kernel
theorem subd5_8_13 : subd5_8 [0, 0] = true := by decide +kernel
theorem subd5_8_14 : subd5_8 [0, 1] = true := by decide +kernel
theorem subd5_8_15 : subd5_8 [0, 2] = true := by decide +kernel
theorem subd5_8_16 : subd5_8 [0, 3] = true := by decide +kernel
theorem subd5_8_17 : subd5_8 [1, -3] = true := by decide +kernel
theorem subd5_8_18 : subd5_8 [1, -2] = true := by decide +kernel
theorem subd5_8_19 : subd5_8 [1, -1] = true := by decide +kernel
theorem subd5_8_20 : subd5_8 [1, 0] = true := by decide +kernel
theorem subd5_8_21 : subd5_8 [1, 1] = true := by decide +kernel
theorem subd5_8_22 : subd5_8 [1, 2] = true := by decide +kernel
theorem subd5_8_23 : subd5_8 [1, 3] = true := by decide +kernel
theorem subd5_8_24 : subd5_8 [2] = true := by decide +kernel
theorem subd5_8_25 : subd5_8 [3] = true := by decide +kernel
theorem sbd5_8_0 : ∀ q ∈ blkd5_8_0, subd5_8 q = true := by
  unfold blkd5_8_0
  exact List.forall_mem_cons.2 ⟨subd5_8_0, List.forall_mem_cons.2 ⟨subd5_8_1, List.forall_mem_cons.2 ⟨subd5_8_2, List.forall_mem_cons.2 ⟨subd5_8_3, List.forall_mem_cons.2 ⟨subd5_8_4, List.forall_mem_cons.2 ⟨subd5_8_5, List.forall_mem_cons.2 ⟨subd5_8_6, List.forall_mem_cons.2 ⟨subd5_8_7, List.forall_mem_cons.2 ⟨subd5_8_8, List.forall_mem_cons.2 ⟨subd5_8_9, List.forall_mem_cons.2 ⟨subd5_8_10, List.forall_mem_cons.2 ⟨subd5_8_11, List.forall_mem_cons.2 ⟨subd5_8_12, List.forall_mem_cons.2 ⟨subd5_8_13, List.forall_mem_cons.2 ⟨subd5_8_14, List.forall_mem_cons.2 ⟨subd5_8_15, List.forall_mem_cons.2 ⟨subd5_8_16, List.forall_mem_cons.2 ⟨subd5_8_17, List.forall_mem_cons.2 ⟨subd5_8_18, List.forall_mem_cons.2 ⟨subd5_8_19, List.forall_mem_cons.2 ⟨subd5_8_20, List.forall_mem_cons.2 ⟨subd5_8_21, List.forall_mem_cons.2 ⟨subd5_8_22, List.forall_mem_cons.2 ⟨subd5_8_23, List.forall_mem_cons.2 ⟨subd5_8_24, List.forall_mem_cons.2 ⟨subd5_8_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_9 : ldCheck G d5_9.U d5_9.ms ldd5_9 = true := by decide +kernel
theorem pre_okd5_9 : subPre G cell5 d5_9 = true := by decide +kernel
theorem subd5_9_0 : subd5_9 [] = true := by decide +kernel
theorem sbd5_9_0 : ∀ q ∈ blkd5_9_0, subd5_9 q = true := by
  unfold blkd5_9_0
  exact List.forall_mem_cons.2 ⟨subd5_9_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
