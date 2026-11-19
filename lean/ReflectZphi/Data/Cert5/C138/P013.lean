import ReflectZphi.Data.Cert5.C138.Base

namespace ReflectZphi.Data.Cert5.C138

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_nil _⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [-2] = true := by decide +kernel
theorem subd18_1_1 : subd18_1 [-1, -4] = true := by decide +kernel
theorem subd18_1_2 : subd18_1 [-1, -3] = true := by decide +kernel
theorem subd18_1_3 : subd18_1 [-1, -2] = true := by decide +kernel
theorem subd18_1_4 : subd18_1 [-1, -1] = true := by decide +kernel
theorem subd18_1_5 : subd18_1 [-1, 0] = true := by decide +kernel
theorem subd18_1_6 : subd18_1 [-1, 1] = true := by decide +kernel
theorem subd18_1_7 : subd18_1 [-1, 2] = true := by decide +kernel
theorem subd18_1_8 : subd18_1 [-1, 3] = true := by decide +kernel
theorem subd18_1_9 : subd18_1 [-1, 4] = true := by decide +kernel
theorem subd18_1_10 : subd18_1 [0, -5] = true := by decide +kernel
theorem subd18_1_11 : subd18_1 [0, -4] = true := by decide +kernel
theorem subd18_1_12 : subd18_1 [0, -3] = true := by decide +kernel
theorem subd18_1_13 : subd18_1 [0, -2] = true := by decide +kernel
theorem subd18_1_14 : subd18_1 [0, -1] = true := by decide +kernel
theorem subd18_1_15 : subd18_1 [0, 0] = true := by decide +kernel
theorem subd18_1_16 : subd18_1 [0, 1] = true := by decide +kernel
theorem subd18_1_17 : subd18_1 [0, 2] = true := by decide +kernel
theorem subd18_1_18 : subd18_1 [0, 3] = true := by decide +kernel
theorem subd18_1_19 : subd18_1 [0, 4] = true := by decide +kernel
theorem subd18_1_20 : subd18_1 [1, -5] = true := by decide +kernel
theorem subd18_1_21 : subd18_1 [1, -4] = true := by decide +kernel
theorem subd18_1_22 : subd18_1 [1, -3] = true := by decide +kernel
theorem subd18_1_23 : subd18_1 [1, -2] = true := by decide +kernel
theorem subd18_1_24 : subd18_1 [1, -1] = true := by decide +kernel
theorem subd18_1_25 : subd18_1 [1, 0] = true := by decide +kernel
theorem subd18_1_26 : subd18_1 [1, 1] = true := by decide +kernel
theorem subd18_1_27 : subd18_1 [1, 2] = true := by decide +kernel
theorem subd18_1_28 : subd18_1 [1, 3] = true := by decide +kernel
theorem subd18_1_29 : subd18_1 [2] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_cons.2 ⟨subd18_1_1, List.forall_mem_cons.2 ⟨subd18_1_2, List.forall_mem_cons.2 ⟨subd18_1_3, List.forall_mem_cons.2 ⟨subd18_1_4, List.forall_mem_cons.2 ⟨subd18_1_5, List.forall_mem_cons.2 ⟨subd18_1_6, List.forall_mem_cons.2 ⟨subd18_1_7, List.forall_mem_cons.2 ⟨subd18_1_8, List.forall_mem_cons.2 ⟨subd18_1_9, List.forall_mem_cons.2 ⟨subd18_1_10, List.forall_mem_cons.2 ⟨subd18_1_11, List.forall_mem_cons.2 ⟨subd18_1_12, List.forall_mem_cons.2 ⟨subd18_1_13, List.forall_mem_cons.2 ⟨subd18_1_14, List.forall_mem_cons.2 ⟨subd18_1_15, List.forall_mem_cons.2 ⟨subd18_1_16, List.forall_mem_cons.2 ⟨subd18_1_17, List.forall_mem_cons.2 ⟨subd18_1_18, List.forall_mem_cons.2 ⟨subd18_1_19, List.forall_mem_cons.2 ⟨subd18_1_20, List.forall_mem_cons.2 ⟨subd18_1_21, List.forall_mem_cons.2 ⟨subd18_1_22, List.forall_mem_cons.2 ⟨subd18_1_23, List.forall_mem_cons.2 ⟨subd18_1_24, List.forall_mem_cons.2 ⟨subd18_1_25, List.forall_mem_cons.2 ⟨subd18_1_26, List.forall_mem_cons.2 ⟨subd18_1_27, List.forall_mem_cons.2 ⟨subd18_1_28, List.forall_mem_cons.2 ⟨subd18_1_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel
theorem subd18_2_0 : subd18_2 [] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_nil _⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [-2] = true := by decide +kernel
theorem subd18_3_1 : subd18_3 [-1] = true := by decide +kernel
theorem subd18_3_2 : subd18_3 [0] = true := by decide +kernel
theorem subd18_3_3 : subd18_3 [1] = true := by decide +kernel
theorem subd18_3_4 : subd18_3 [2] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_cons.2 ⟨subd18_3_1, List.forall_mem_cons.2 ⟨subd18_3_2, List.forall_mem_cons.2 ⟨subd18_3_3, List.forall_mem_cons.2 ⟨subd18_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C138
