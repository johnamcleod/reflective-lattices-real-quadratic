import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
theorem ld_okd0_2 : ldCheck G d0_2.U d0_2.ms ldd0_2 = true := by decide +kernel
theorem pre_okd0_2 : subPre G cell0 d0_2 = true := by decide +kernel
theorem subd0_2_0 : subd0_2 [-1] = true := by decide +kernel
theorem subd0_2_1 : subd0_2 [0] = true := by decide +kernel
theorem subd0_2_2 : subd0_2 [1] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_cons.2 ⟨subd0_2_1, List.forall_mem_cons.2 ⟨subd0_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_nil _⟩
theorem ld_okd0_4 : ldCheck G d0_4.U d0_4.ms ldd0_4 = true := by decide +kernel
theorem pre_okd0_4 : subPre G cell0 d0_4 = true := by decide +kernel
theorem subd0_4_0 : subd0_4 [-3] = true := by decide +kernel
theorem subd0_4_1 : subd0_4 [-2] = true := by decide +kernel
theorem subd0_4_2 : subd0_4 [-1, -4] = true := by decide +kernel
theorem subd0_4_3 : subd0_4 [-1, -3] = true := by decide +kernel
theorem subd0_4_4 : subd0_4 [-1, -2] = true := by decide +kernel
theorem subd0_4_5 : subd0_4 [-1, -1] = true := by decide +kernel
theorem subd0_4_6 : subd0_4 [-1, 0] = true := by decide +kernel
theorem subd0_4_7 : subd0_4 [-1, 1] = true := by decide +kernel
theorem subd0_4_8 : subd0_4 [-1, 2] = true := by decide +kernel
theorem subd0_4_9 : subd0_4 [-1, 3] = true := by decide +kernel
theorem subd0_4_10 : subd0_4 [0, -4] = true := by decide +kernel
theorem subd0_4_11 : subd0_4 [0, -3] = true := by decide +kernel
theorem subd0_4_12 : subd0_4 [0, -2] = true := by decide +kernel
theorem subd0_4_13 : subd0_4 [0, -1] = true := by decide +kernel
theorem subd0_4_14 : subd0_4 [0, 0] = true := by decide +kernel
theorem subd0_4_15 : subd0_4 [0, 1] = true := by decide +kernel
theorem subd0_4_16 : subd0_4 [0, 2] = true := by decide +kernel
theorem subd0_4_17 : subd0_4 [0, 3] = true := by decide +kernel
theorem subd0_4_18 : subd0_4 [1, -4] = true := by decide +kernel
theorem subd0_4_19 : subd0_4 [1, -3] = true := by decide +kernel
theorem subd0_4_20 : subd0_4 [1, -2] = true := by decide +kernel
theorem subd0_4_21 : subd0_4 [1, -1] = true := by decide +kernel
theorem subd0_4_22 : subd0_4 [1, 0] = true := by decide +kernel
theorem subd0_4_23 : subd0_4 [1, 1] = true := by decide +kernel
theorem subd0_4_24 : subd0_4 [1, 2] = true := by decide +kernel
theorem subd0_4_25 : subd0_4 [1, 3] = true := by decide +kernel
theorem subd0_4_26 : subd0_4 [2] = true := by decide +kernel
theorem subd0_4_27 : subd0_4 [3] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_cons.2 ⟨subd0_4_1, List.forall_mem_cons.2 ⟨subd0_4_2, List.forall_mem_cons.2 ⟨subd0_4_3, List.forall_mem_cons.2 ⟨subd0_4_4, List.forall_mem_cons.2 ⟨subd0_4_5, List.forall_mem_cons.2 ⟨subd0_4_6, List.forall_mem_cons.2 ⟨subd0_4_7, List.forall_mem_cons.2 ⟨subd0_4_8, List.forall_mem_cons.2 ⟨subd0_4_9, List.forall_mem_cons.2 ⟨subd0_4_10, List.forall_mem_cons.2 ⟨subd0_4_11, List.forall_mem_cons.2 ⟨subd0_4_12, List.forall_mem_cons.2 ⟨subd0_4_13, List.forall_mem_cons.2 ⟨subd0_4_14, List.forall_mem_cons.2 ⟨subd0_4_15, List.forall_mem_cons.2 ⟨subd0_4_16, List.forall_mem_cons.2 ⟨subd0_4_17, List.forall_mem_cons.2 ⟨subd0_4_18, List.forall_mem_cons.2 ⟨subd0_4_19, List.forall_mem_cons.2 ⟨subd0_4_20, List.forall_mem_cons.2 ⟨subd0_4_21, List.forall_mem_cons.2 ⟨subd0_4_22, List.forall_mem_cons.2 ⟨subd0_4_23, List.forall_mem_cons.2 ⟨subd0_4_24, List.forall_mem_cons.2 ⟨subd0_4_25, List.forall_mem_cons.2 ⟨subd0_4_26, List.forall_mem_cons.2 ⟨subd0_4_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_5 : ldCheck G d0_5.U d0_5.ms ldd0_5 = true := by decide +kernel
theorem pre_okd0_5 : subPre G cell0 d0_5 = true := by decide +kernel
theorem subd0_5_0 : subd0_5 [-3] = true := by decide +kernel
theorem subd0_5_1 : subd0_5 [-2] = true := by decide +kernel
theorem subd0_5_2 : subd0_5 [-1, -4] = true := by decide +kernel
theorem subd0_5_3 : subd0_5 [-1, -3] = true := by decide +kernel
theorem subd0_5_4 : subd0_5 [-1, -2] = true := by decide +kernel
theorem subd0_5_5 : subd0_5 [-1, -1] = true := by decide +kernel
theorem subd0_5_6 : subd0_5 [-1, 0] = true := by decide +kernel
theorem subd0_5_7 : subd0_5 [-1, 1] = true := by decide +kernel
theorem subd0_5_8 : subd0_5 [-1, 2] = true := by decide +kernel
theorem subd0_5_9 : subd0_5 [0, -4] = true := by decide +kernel
theorem subd0_5_10 : subd0_5 [0, -3] = true := by decide +kernel
theorem subd0_5_11 : subd0_5 [0, -2] = true := by decide +kernel
theorem subd0_5_12 : subd0_5 [0, -1] = true := by decide +kernel
theorem subd0_5_13 : subd0_5 [0, 0] = true := by decide +kernel
theorem subd0_5_14 : subd0_5 [0, 1] = true := by decide +kernel
theorem subd0_5_15 : subd0_5 [0, 2] = true := by decide +kernel
theorem subd0_5_16 : subd0_5 [0, 3] = true := by decide +kernel
theorem subd0_5_17 : subd0_5 [1, -3] = true := by decide +kernel
theorem subd0_5_18 : subd0_5 [1, -2] = true := by decide +kernel
theorem subd0_5_19 : subd0_5 [1, -1] = true := by decide +kernel
theorem subd0_5_20 : subd0_5 [1, 0] = true := by decide +kernel
theorem subd0_5_21 : subd0_5 [1, 1] = true := by decide +kernel
theorem subd0_5_22 : subd0_5 [1, 2] = true := by decide +kernel
theorem subd0_5_23 : subd0_5 [1, 3] = true := by decide +kernel
theorem subd0_5_24 : subd0_5 [2] = true := by decide +kernel
theorem subd0_5_25 : subd0_5 [3] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_cons.2 ⟨subd0_5_1, List.forall_mem_cons.2 ⟨subd0_5_2, List.forall_mem_cons.2 ⟨subd0_5_3, List.forall_mem_cons.2 ⟨subd0_5_4, List.forall_mem_cons.2 ⟨subd0_5_5, List.forall_mem_cons.2 ⟨subd0_5_6, List.forall_mem_cons.2 ⟨subd0_5_7, List.forall_mem_cons.2 ⟨subd0_5_8, List.forall_mem_cons.2 ⟨subd0_5_9, List.forall_mem_cons.2 ⟨subd0_5_10, List.forall_mem_cons.2 ⟨subd0_5_11, List.forall_mem_cons.2 ⟨subd0_5_12, List.forall_mem_cons.2 ⟨subd0_5_13, List.forall_mem_cons.2 ⟨subd0_5_14, List.forall_mem_cons.2 ⟨subd0_5_15, List.forall_mem_cons.2 ⟨subd0_5_16, List.forall_mem_cons.2 ⟨subd0_5_17, List.forall_mem_cons.2 ⟨subd0_5_18, List.forall_mem_cons.2 ⟨subd0_5_19, List.forall_mem_cons.2 ⟨subd0_5_20, List.forall_mem_cons.2 ⟨subd0_5_21, List.forall_mem_cons.2 ⟨subd0_5_22, List.forall_mem_cons.2 ⟨subd0_5_23, List.forall_mem_cons.2 ⟨subd0_5_24, List.forall_mem_cons.2 ⟨subd0_5_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
