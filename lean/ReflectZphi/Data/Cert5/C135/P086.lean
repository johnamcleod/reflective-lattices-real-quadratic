import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_2_0 : subd15_2 [-2] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [-1, -3] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [-1, -2] = true := by decide +kernel
theorem subd15_2_3 : subd15_2 [-1, -1] = true := by decide +kernel
theorem subd15_2_4 : subd15_2 [-1, 0] = true := by decide +kernel
theorem subd15_2_5 : subd15_2 [-1, 1] = true := by decide +kernel
theorem subd15_2_6 : subd15_2 [-1, 2] = true := by decide +kernel
theorem subd15_2_7 : subd15_2 [0, -3] = true := by decide +kernel
theorem subd15_2_8 : subd15_2 [0, -2] = true := by decide +kernel
theorem subd15_2_9 : subd15_2 [0, -1] = true := by decide +kernel
theorem subd15_2_10 : subd15_2 [0, 0] = true := by decide +kernel
theorem subd15_2_11 : subd15_2 [0, 1] = true := by decide +kernel
theorem subd15_2_12 : subd15_2 [0, 2] = true := by decide +kernel
theorem subd15_2_13 : subd15_2 [1, -3] = true := by decide +kernel
theorem subd15_2_14 : subd15_2 [1, -2] = true := by decide +kernel
theorem subd15_2_15 : subd15_2 [1, -1] = true := by decide +kernel
theorem subd15_2_16 : subd15_2 [1, 0] = true := by decide +kernel
theorem subd15_2_17 : subd15_2 [1, 1] = true := by decide +kernel
theorem subd15_2_18 : subd15_2 [1, 2] = true := by decide +kernel
theorem subd15_2_19 : subd15_2 [2] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_cons.2 ⟨subd15_2_3, List.forall_mem_cons.2 ⟨subd15_2_4, List.forall_mem_cons.2 ⟨subd15_2_5, List.forall_mem_cons.2 ⟨subd15_2_6, List.forall_mem_cons.2 ⟨subd15_2_7, List.forall_mem_cons.2 ⟨subd15_2_8, List.forall_mem_cons.2 ⟨subd15_2_9, List.forall_mem_cons.2 ⟨subd15_2_10, List.forall_mem_cons.2 ⟨subd15_2_11, List.forall_mem_cons.2 ⟨subd15_2_12, List.forall_mem_cons.2 ⟨subd15_2_13, List.forall_mem_cons.2 ⟨subd15_2_14, List.forall_mem_cons.2 ⟨subd15_2_15, List.forall_mem_cons.2 ⟨subd15_2_16, List.forall_mem_cons.2 ⟨subd15_2_17, List.forall_mem_cons.2 ⟨subd15_2_18, List.forall_mem_cons.2 ⟨subd15_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [-3] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [-2, -3] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [-2, -2] = true := by decide +kernel
theorem subd15_3_3 : subd15_3 [-2, -1] = true := by decide +kernel
theorem subd15_3_4 : subd15_3 [-2, 0] = true := by decide +kernel
theorem subd15_3_5 : subd15_3 [-2, 1] = true := by decide +kernel
theorem subd15_3_6 : subd15_3 [-1, -3] = true := by decide +kernel
theorem subd15_3_7 : subd15_3 [-1, -2] = true := by decide +kernel
theorem subd15_3_8 : subd15_3 [-1, -1] = true := by decide +kernel
theorem subd15_3_9 : subd15_3 [-1, 0] = true := by decide +kernel
theorem subd15_3_10 : subd15_3 [-1, 1] = true := by decide +kernel
theorem subd15_3_11 : subd15_3 [-1, 2] = true := by decide +kernel
theorem subd15_3_12 : subd15_3 [0, -3] = true := by decide +kernel
theorem subd15_3_13 : subd15_3 [0, -2] = true := by decide +kernel
theorem subd15_3_14 : subd15_3 [0, -1] = true := by decide +kernel
theorem subd15_3_15 : subd15_3 [0, 0] = true := by decide +kernel
theorem subd15_3_16 : subd15_3 [0, 1] = true := by decide +kernel
theorem subd15_3_17 : subd15_3 [0, 2] = true := by decide +kernel
theorem subd15_3_18 : subd15_3 [1, -3] = true := by decide +kernel
theorem subd15_3_19 : subd15_3 [1, -2] = true := by decide +kernel
theorem subd15_3_20 : subd15_3 [1, -1] = true := by decide +kernel
theorem subd15_3_21 : subd15_3 [1, 0] = true := by decide +kernel
theorem subd15_3_22 : subd15_3 [1, 1] = true := by decide +kernel
theorem subd15_3_23 : subd15_3 [1, 2] = true := by decide +kernel
theorem subd15_3_24 : subd15_3 [2, -2] = true := by decide +kernel
theorem subd15_3_25 : subd15_3 [2, -1] = true := by decide +kernel
theorem subd15_3_26 : subd15_3 [2, 0] = true := by decide +kernel
theorem subd15_3_27 : subd15_3 [2, 1] = true := by decide +kernel
theorem subd15_3_28 : subd15_3 [2, 2] = true := by decide +kernel
theorem subd15_3_29 : subd15_3 [3] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_cons.2 ⟨subd15_3_3, List.forall_mem_cons.2 ⟨subd15_3_4, List.forall_mem_cons.2 ⟨subd15_3_5, List.forall_mem_cons.2 ⟨subd15_3_6, List.forall_mem_cons.2 ⟨subd15_3_7, List.forall_mem_cons.2 ⟨subd15_3_8, List.forall_mem_cons.2 ⟨subd15_3_9, List.forall_mem_cons.2 ⟨subd15_3_10, List.forall_mem_cons.2 ⟨subd15_3_11, List.forall_mem_cons.2 ⟨subd15_3_12, List.forall_mem_cons.2 ⟨subd15_3_13, List.forall_mem_cons.2 ⟨subd15_3_14, List.forall_mem_cons.2 ⟨subd15_3_15, List.forall_mem_cons.2 ⟨subd15_3_16, List.forall_mem_cons.2 ⟨subd15_3_17, List.forall_mem_cons.2 ⟨subd15_3_18, List.forall_mem_cons.2 ⟨subd15_3_19, List.forall_mem_cons.2 ⟨subd15_3_20, List.forall_mem_cons.2 ⟨subd15_3_21, List.forall_mem_cons.2 ⟨subd15_3_22, List.forall_mem_cons.2 ⟨subd15_3_23, List.forall_mem_cons.2 ⟨subd15_3_24, List.forall_mem_cons.2 ⟨subd15_3_25, List.forall_mem_cons.2 ⟨subd15_3_26, List.forall_mem_cons.2 ⟨subd15_3_27, List.forall_mem_cons.2 ⟨subd15_3_28, List.forall_mem_cons.2 ⟨subd15_3_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_4 : ldCheck G d15_4.U d15_4.ms ldd15_4 = true := by decide +kernel
theorem pre_okd15_4 : subPre G cell15 d15_4 = true := by decide +kernel
theorem subd15_4_0 : subd15_4 [-3] = true := by decide +kernel
theorem subd15_4_1 : subd15_4 [-2] = true := by decide +kernel
theorem subd15_4_2 : subd15_4 [-1, -4] = true := by decide +kernel
theorem subd15_4_3 : subd15_4 [-1, -3] = true := by decide +kernel
theorem subd15_4_4 : subd15_4 [-1, -2] = true := by decide +kernel
theorem subd15_4_5 : subd15_4 [-1, -1] = true := by decide +kernel
theorem subd15_4_6 : subd15_4 [-1, 0] = true := by decide +kernel
theorem subd15_4_7 : subd15_4 [-1, 1] = true := by decide +kernel
theorem subd15_4_8 : subd15_4 [-1, 2] = true := by decide +kernel
theorem subd15_4_9 : subd15_4 [0, -3] = true := by decide +kernel
theorem subd15_4_10 : subd15_4 [0, -2] = true := by decide +kernel
theorem subd15_4_11 : subd15_4 [0, -1] = true := by decide +kernel
theorem subd15_4_12 : subd15_4 [0, 0] = true := by decide +kernel
theorem subd15_4_13 : subd15_4 [0, 1] = true := by decide +kernel
theorem subd15_4_14 : subd15_4 [0, 2] = true := by decide +kernel
theorem subd15_4_15 : subd15_4 [1, -3] = true := by decide +kernel
theorem subd15_4_16 : subd15_4 [1, -2] = true := by decide +kernel
theorem subd15_4_17 : subd15_4 [1, -1] = true := by decide +kernel
theorem subd15_4_18 : subd15_4 [1, 0] = true := by decide +kernel
theorem subd15_4_19 : subd15_4 [1, 1] = true := by decide +kernel
theorem subd15_4_20 : subd15_4 [1, 2] = true := by decide +kernel
theorem subd15_4_21 : subd15_4 [1, 3] = true := by decide +kernel
theorem subd15_4_22 : subd15_4 [2] = true := by decide +kernel
theorem subd15_4_23 : subd15_4 [3] = true := by decide +kernel
theorem sbd15_4_0 : ∀ q ∈ blkd15_4_0, subd15_4 q = true := by
  unfold blkd15_4_0
  exact List.forall_mem_cons.2 ⟨subd15_4_0, List.forall_mem_cons.2 ⟨subd15_4_1, List.forall_mem_cons.2 ⟨subd15_4_2, List.forall_mem_cons.2 ⟨subd15_4_3, List.forall_mem_cons.2 ⟨subd15_4_4, List.forall_mem_cons.2 ⟨subd15_4_5, List.forall_mem_cons.2 ⟨subd15_4_6, List.forall_mem_cons.2 ⟨subd15_4_7, List.forall_mem_cons.2 ⟨subd15_4_8, List.forall_mem_cons.2 ⟨subd15_4_9, List.forall_mem_cons.2 ⟨subd15_4_10, List.forall_mem_cons.2 ⟨subd15_4_11, List.forall_mem_cons.2 ⟨subd15_4_12, List.forall_mem_cons.2 ⟨subd15_4_13, List.forall_mem_cons.2 ⟨subd15_4_14, List.forall_mem_cons.2 ⟨subd15_4_15, List.forall_mem_cons.2 ⟨subd15_4_16, List.forall_mem_cons.2 ⟨subd15_4_17, List.forall_mem_cons.2 ⟨subd15_4_18, List.forall_mem_cons.2 ⟨subd15_4_19, List.forall_mem_cons.2 ⟨subd15_4_20, List.forall_mem_cons.2 ⟨subd15_4_21, List.forall_mem_cons.2 ⟨subd15_4_22, List.forall_mem_cons.2 ⟨subd15_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_5 : ldCheck G d15_5.U d15_5.ms ldd15_5 = true := by decide +kernel
theorem pre_okd15_5 : subPre G cell15 d15_5 = true := by decide +kernel
theorem subd15_5_0 : subd15_5 [-2] = true := by decide +kernel
theorem subd15_5_1 : subd15_5 [-1] = true := by decide +kernel
theorem subd15_5_2 : subd15_5 [0, -3] = true := by decide +kernel
theorem subd15_5_3 : subd15_5 [0, -2] = true := by decide +kernel
theorem subd15_5_4 : subd15_5 [0, -1] = true := by decide +kernel
theorem subd15_5_5 : subd15_5 [0, 0] = true := by decide +kernel
theorem subd15_5_6 : subd15_5 [0, 1] = true := by decide +kernel
theorem subd15_5_7 : subd15_5 [0, 2] = true := by decide +kernel
theorem subd15_5_8 : subd15_5 [1] = true := by decide +kernel
theorem subd15_5_9 : subd15_5 [2] = true := by decide +kernel
theorem sbd15_5_0 : ∀ q ∈ blkd15_5_0, subd15_5 q = true := by
  unfold blkd15_5_0
  exact List.forall_mem_cons.2 ⟨subd15_5_0, List.forall_mem_cons.2 ⟨subd15_5_1, List.forall_mem_cons.2 ⟨subd15_5_2, List.forall_mem_cons.2 ⟨subd15_5_3, List.forall_mem_cons.2 ⟨subd15_5_4, List.forall_mem_cons.2 ⟨subd15_5_5, List.forall_mem_cons.2 ⟨subd15_5_6, List.forall_mem_cons.2 ⟨subd15_5_7, List.forall_mem_cons.2 ⟨subd15_5_8, List.forall_mem_cons.2 ⟨subd15_5_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_6 : ldCheck G d15_6.U d15_6.ms ldd15_6 = true := by decide +kernel
theorem pre_okd15_6 : subPre G cell15 d15_6 = true := by decide +kernel
theorem subd15_6_0 : subd15_6 [-2] = true := by decide +kernel
theorem subd15_6_1 : subd15_6 [-1] = true := by decide +kernel
theorem subd15_6_2 : subd15_6 [0] = true := by decide +kernel
theorem subd15_6_3 : subd15_6 [1] = true := by decide +kernel
theorem subd15_6_4 : subd15_6 [2] = true := by decide +kernel
theorem sbd15_6_0 : ∀ q ∈ blkd15_6_0, subd15_6 q = true := by
  unfold blkd15_6_0
  exact List.forall_mem_cons.2 ⟨subd15_6_0, List.forall_mem_cons.2 ⟨subd15_6_1, List.forall_mem_cons.2 ⟨subd15_6_2, List.forall_mem_cons.2 ⟨subd15_6_3, List.forall_mem_cons.2 ⟨subd15_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
