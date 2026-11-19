import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-2] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [2] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-1] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [0] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [1] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-2] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [2] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-1] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [0] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [2] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [2] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [3] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
