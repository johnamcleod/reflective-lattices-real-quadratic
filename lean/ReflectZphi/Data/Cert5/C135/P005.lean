import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-2] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-1, 0] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [0, -1] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [0, 0] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [0, 1] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [1, -2] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [1, 0] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [2] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [-2] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-1] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [0, -2] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [0, -1] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [0, 0] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [0, 1] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [0, 2] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [1] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [2] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-2] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [0] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [0] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [2] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [2] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [3] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
