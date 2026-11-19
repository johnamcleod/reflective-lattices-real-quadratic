import ReflectZphi.Data.Cert5.C061.Base

namespace ReflectZphi.Data.Cert5.C061

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_0 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [2] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-4] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [0, 3] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [1, 3] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [2] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [3] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [4] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-2] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-1] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [0] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [1] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [2] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [1] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [2] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [3] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C061
