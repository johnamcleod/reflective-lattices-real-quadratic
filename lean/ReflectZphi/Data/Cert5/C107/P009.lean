import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_7_0 : subd5_7 [-2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [0, 1] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [2] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-2] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [2] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [2] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
