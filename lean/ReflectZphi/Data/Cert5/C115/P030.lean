import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_7_0 : subd18_7 [-2] = true := by decide +kernel
theorem subd18_7_1 : subd18_7 [-1] = true := by decide +kernel
theorem subd18_7_2 : subd18_7 [0] = true := by decide +kernel
theorem subd18_7_3 : subd18_7 [1] = true := by decide +kernel
theorem subd18_7_4 : subd18_7 [2] = true := by decide +kernel
theorem sbd18_7_0 : ∀ q ∈ blkd18_7_0, subd18_7 q = true := by
  unfold blkd18_7_0
  exact List.forall_mem_cons.2 ⟨subd18_7_0, List.forall_mem_cons.2 ⟨subd18_7_1, List.forall_mem_cons.2 ⟨subd18_7_2, List.forall_mem_cons.2 ⟨subd18_7_3, List.forall_mem_cons.2 ⟨subd18_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd18_8 : ldCheck G d18_8.U d18_8.ms ldd18_8 = true := by decide +kernel
theorem pre_okd18_8 : subPre G cell18 d18_8 = true := by decide +kernel
theorem subd18_8_0 : subd18_8 [-3] = true := by decide +kernel
theorem subd18_8_1 : subd18_8 [-2] = true := by decide +kernel
theorem subd18_8_2 : subd18_8 [-1, -3] = true := by decide +kernel
theorem subd18_8_3 : subd18_8 [-1, -2] = true := by decide +kernel
theorem subd18_8_4 : subd18_8 [-1, -1] = true := by decide +kernel
theorem subd18_8_5 : subd18_8 [-1, 0] = true := by decide +kernel
theorem subd18_8_6 : subd18_8 [-1, 1] = true := by decide +kernel
theorem subd18_8_7 : subd18_8 [-1, 2] = true := by decide +kernel
theorem subd18_8_8 : subd18_8 [-1, 3] = true := by decide +kernel
theorem subd18_8_9 : subd18_8 [0, -4] = true := by decide +kernel
theorem subd18_8_10 : subd18_8 [0, -3] = true := by decide +kernel
theorem subd18_8_11 : subd18_8 [0, -2] = true := by decide +kernel
theorem subd18_8_12 : subd18_8 [0, -1] = true := by decide +kernel
theorem subd18_8_13 : subd18_8 [0, 0] = true := by decide +kernel
theorem subd18_8_14 : subd18_8 [0, 1] = true := by decide +kernel
theorem subd18_8_15 : subd18_8 [0, 2] = true := by decide +kernel
theorem subd18_8_16 : subd18_8 [0, 3] = true := by decide +kernel
theorem subd18_8_17 : subd18_8 [1, -4] = true := by decide +kernel
theorem subd18_8_18 : subd18_8 [1, -3] = true := by decide +kernel
theorem subd18_8_19 : subd18_8 [1, -2] = true := by decide +kernel
theorem subd18_8_20 : subd18_8 [1, -1] = true := by decide +kernel
theorem subd18_8_21 : subd18_8 [1, 0] = true := by decide +kernel
theorem subd18_8_22 : subd18_8 [1, 1] = true := by decide +kernel
theorem subd18_8_23 : subd18_8 [1, 2] = true := by decide +kernel
theorem subd18_8_24 : subd18_8 [2] = true := by decide +kernel
theorem subd18_8_25 : subd18_8 [3] = true := by decide +kernel
theorem sbd18_8_0 : ∀ q ∈ blkd18_8_0, subd18_8 q = true := by
  unfold blkd18_8_0
  exact List.forall_mem_cons.2 ⟨subd18_8_0, List.forall_mem_cons.2 ⟨subd18_8_1, List.forall_mem_cons.2 ⟨subd18_8_2, List.forall_mem_cons.2 ⟨subd18_8_3, List.forall_mem_cons.2 ⟨subd18_8_4, List.forall_mem_cons.2 ⟨subd18_8_5, List.forall_mem_cons.2 ⟨subd18_8_6, List.forall_mem_cons.2 ⟨subd18_8_7, List.forall_mem_cons.2 ⟨subd18_8_8, List.forall_mem_cons.2 ⟨subd18_8_9, List.forall_mem_cons.2 ⟨subd18_8_10, List.forall_mem_cons.2 ⟨subd18_8_11, List.forall_mem_cons.2 ⟨subd18_8_12, List.forall_mem_cons.2 ⟨subd18_8_13, List.forall_mem_cons.2 ⟨subd18_8_14, List.forall_mem_cons.2 ⟨subd18_8_15, List.forall_mem_cons.2 ⟨subd18_8_16, List.forall_mem_cons.2 ⟨subd18_8_17, List.forall_mem_cons.2 ⟨subd18_8_18, List.forall_mem_cons.2 ⟨subd18_8_19, List.forall_mem_cons.2 ⟨subd18_8_20, List.forall_mem_cons.2 ⟨subd18_8_21, List.forall_mem_cons.2 ⟨subd18_8_22, List.forall_mem_cons.2 ⟨subd18_8_23, List.forall_mem_cons.2 ⟨subd18_8_24, List.forall_mem_cons.2 ⟨subd18_8_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_9 : ldCheck G d18_9.U d18_9.ms ldd18_9 = true := by decide +kernel
theorem pre_okd18_9 : subPre G cell18 d18_9 = true := by decide +kernel
theorem subd18_9_0 : subd18_9 [] = true := by decide +kernel
theorem sbd18_9_0 : ∀ q ∈ blkd18_9_0, subd18_9 q = true := by
  unfold blkd18_9_0
  exact List.forall_mem_cons.2 ⟨subd18_9_0, List.forall_mem_nil _⟩
theorem ld_okd18_10 : ldCheck G d18_10.U d18_10.ms ldd18_10 = true := by decide +kernel
theorem pre_okd18_10 : subPre G cell18 d18_10 = true := by decide +kernel
theorem subd18_10_0 : subd18_10 [-2] = true := by decide +kernel
theorem subd18_10_1 : subd18_10 [-1] = true := by decide +kernel
theorem subd18_10_2 : subd18_10 [0] = true := by decide +kernel
theorem subd18_10_3 : subd18_10 [1] = true := by decide +kernel
theorem subd18_10_4 : subd18_10 [2] = true := by decide +kernel
theorem sbd18_10_0 : ∀ q ∈ blkd18_10_0, subd18_10 q = true := by
  unfold blkd18_10_0
  exact List.forall_mem_cons.2 ⟨subd18_10_0, List.forall_mem_cons.2 ⟨subd18_10_1, List.forall_mem_cons.2 ⟨subd18_10_2, List.forall_mem_cons.2 ⟨subd18_10_3, List.forall_mem_cons.2 ⟨subd18_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd18_11 : ldCheck G d18_11.U d18_11.ms ldd18_11 = true := by decide +kernel
theorem pre_okd18_11 : subPre G cell18 d18_11 = true := by decide +kernel
theorem subd18_11_0 : subd18_11 [] = true := by decide +kernel
theorem sbd18_11_0 : ∀ q ∈ blkd18_11_0, subd18_11 q = true := by
  unfold blkd18_11_0
  exact List.forall_mem_cons.2 ⟨subd18_11_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
