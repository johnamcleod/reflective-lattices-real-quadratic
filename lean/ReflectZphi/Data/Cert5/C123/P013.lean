import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-1] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [1] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-1, 3] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [0, -4] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [0, 3] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [1, -4] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [2] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-3] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [-1, -3] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [-1, -2] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [-1, -1] = true := by decide +kernel
theorem subd6_5_5 : subd6_5 [-1, 0] = true := by decide +kernel
theorem subd6_5_6 : subd6_5 [-1, 1] = true := by decide +kernel
theorem subd6_5_7 : subd6_5 [-1, 2] = true := by decide +kernel
theorem subd6_5_8 : subd6_5 [0, -4] = true := by decide +kernel
theorem subd6_5_9 : subd6_5 [0, -3] = true := by decide +kernel
theorem subd6_5_10 : subd6_5 [0, -2] = true := by decide +kernel
theorem subd6_5_11 : subd6_5 [0, -1] = true := by decide +kernel
theorem subd6_5_12 : subd6_5 [0, 0] = true := by decide +kernel
theorem subd6_5_13 : subd6_5 [0, 1] = true := by decide +kernel
theorem subd6_5_14 : subd6_5 [0, 2] = true := by decide +kernel
theorem subd6_5_15 : subd6_5 [0, 3] = true := by decide +kernel
theorem subd6_5_16 : subd6_5 [1, -3] = true := by decide +kernel
theorem subd6_5_17 : subd6_5 [1, -2] = true := by decide +kernel
theorem subd6_5_18 : subd6_5 [1, -1] = true := by decide +kernel
theorem subd6_5_19 : subd6_5 [1, 0] = true := by decide +kernel
theorem subd6_5_20 : subd6_5 [1, 1] = true := by decide +kernel
theorem subd6_5_21 : subd6_5 [1, 2] = true := by decide +kernel
theorem subd6_5_22 : subd6_5 [2] = true := by decide +kernel
theorem subd6_5_23 : subd6_5 [3] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_cons.2 ⟨subd6_5_5, List.forall_mem_cons.2 ⟨subd6_5_6, List.forall_mem_cons.2 ⟨subd6_5_7, List.forall_mem_cons.2 ⟨subd6_5_8, List.forall_mem_cons.2 ⟨subd6_5_9, List.forall_mem_cons.2 ⟨subd6_5_10, List.forall_mem_cons.2 ⟨subd6_5_11, List.forall_mem_cons.2 ⟨subd6_5_12, List.forall_mem_cons.2 ⟨subd6_5_13, List.forall_mem_cons.2 ⟨subd6_5_14, List.forall_mem_cons.2 ⟨subd6_5_15, List.forall_mem_cons.2 ⟨subd6_5_16, List.forall_mem_cons.2 ⟨subd6_5_17, List.forall_mem_cons.2 ⟨subd6_5_18, List.forall_mem_cons.2 ⟨subd6_5_19, List.forall_mem_cons.2 ⟨subd6_5_20, List.forall_mem_cons.2 ⟨subd6_5_21, List.forall_mem_cons.2 ⟨subd6_5_22, List.forall_mem_cons.2 ⟨subd6_5_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C123
