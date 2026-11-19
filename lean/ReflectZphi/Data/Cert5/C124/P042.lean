import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_0 : subd8_1 [-2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-2] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-1] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [1] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [2] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-2] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-1] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [0] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [1] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [2] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [0, 2] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [1] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
