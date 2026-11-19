import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem subd6_1_0 : subd6_1 [-1] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-1] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [0] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [2] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-2] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-1] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [1] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [2] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [2] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
