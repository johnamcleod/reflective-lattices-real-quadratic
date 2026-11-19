import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_7 : ldCheck G d17_7.U d17_7.ms ldd17_7 = true := by decide +kernel
theorem pre_okd17_7 : subPre G cell17 d17_7 = true := by decide +kernel
theorem subd17_7_0 : subd17_7 [-1] = true := by decide +kernel
theorem subd17_7_1 : subd17_7 [0] = true := by decide +kernel
theorem subd17_7_2 : subd17_7 [1] = true := by decide +kernel
theorem sbd17_7_0 : ∀ q ∈ blkd17_7_0, subd17_7 q = true := by
  unfold blkd17_7_0
  exact List.forall_mem_cons.2 ⟨subd17_7_0, List.forall_mem_cons.2 ⟨subd17_7_1, List.forall_mem_cons.2 ⟨subd17_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd17_8 : ldCheck G d17_8.U d17_8.ms ldd17_8 = true := by decide +kernel
theorem pre_okd17_8 : subPre G cell17 d17_8 = true := by decide +kernel
theorem subd17_8_0 : subd17_8 [-3] = true := by decide +kernel
theorem subd17_8_1 : subd17_8 [-2] = true := by decide +kernel
theorem subd17_8_2 : subd17_8 [-1, -4] = true := by decide +kernel
theorem subd17_8_3 : subd17_8 [-1, -3] = true := by decide +kernel
theorem subd17_8_4 : subd17_8 [-1, -2] = true := by decide +kernel
theorem subd17_8_5 : subd17_8 [-1, -1] = true := by decide +kernel
theorem subd17_8_6 : subd17_8 [-1, 0] = true := by decide +kernel
theorem subd17_8_7 : subd17_8 [-1, 1] = true := by decide +kernel
theorem subd17_8_8 : subd17_8 [-1, 2] = true := by decide +kernel
theorem subd17_8_9 : subd17_8 [-1, 3] = true := by decide +kernel
theorem subd17_8_10 : subd17_8 [-1, 4] = true := by decide +kernel
theorem subd17_8_11 : subd17_8 [0, -4] = true := by decide +kernel
theorem subd17_8_12 : subd17_8 [0, -3] = true := by decide +kernel
theorem subd17_8_13 : subd17_8 [0, -2] = true := by decide +kernel
theorem subd17_8_14 : subd17_8 [0, -1] = true := by decide +kernel
theorem subd17_8_15 : subd17_8 [0, 0] = true := by decide +kernel
theorem subd17_8_16 : subd17_8 [0, 1] = true := by decide +kernel
theorem subd17_8_17 : subd17_8 [0, 2] = true := by decide +kernel
theorem subd17_8_18 : subd17_8 [0, 3] = true := by decide +kernel
theorem subd17_8_19 : subd17_8 [1, -5] = true := by decide +kernel
theorem subd17_8_20 : subd17_8 [1, -4] = true := by decide +kernel
theorem subd17_8_21 : subd17_8 [1, -3] = true := by decide +kernel
theorem subd17_8_22 : subd17_8 [1, -2] = true := by decide +kernel
theorem subd17_8_23 : subd17_8 [1, -1] = true := by decide +kernel
theorem subd17_8_24 : subd17_8 [1, 0] = true := by decide +kernel
theorem subd17_8_25 : subd17_8 [1, 1] = true := by decide +kernel
theorem subd17_8_26 : subd17_8 [1, 2] = true := by decide +kernel
theorem subd17_8_27 : subd17_8 [1, 3] = true := by decide +kernel
theorem subd17_8_28 : subd17_8 [2] = true := by decide +kernel
theorem subd17_8_29 : subd17_8 [3] = true := by decide +kernel
theorem sbd17_8_0 : ∀ q ∈ blkd17_8_0, subd17_8 q = true := by
  unfold blkd17_8_0
  exact List.forall_mem_cons.2 ⟨subd17_8_0, List.forall_mem_cons.2 ⟨subd17_8_1, List.forall_mem_cons.2 ⟨subd17_8_2, List.forall_mem_cons.2 ⟨subd17_8_3, List.forall_mem_cons.2 ⟨subd17_8_4, List.forall_mem_cons.2 ⟨subd17_8_5, List.forall_mem_cons.2 ⟨subd17_8_6, List.forall_mem_cons.2 ⟨subd17_8_7, List.forall_mem_cons.2 ⟨subd17_8_8, List.forall_mem_cons.2 ⟨subd17_8_9, List.forall_mem_cons.2 ⟨subd17_8_10, List.forall_mem_cons.2 ⟨subd17_8_11, List.forall_mem_cons.2 ⟨subd17_8_12, List.forall_mem_cons.2 ⟨subd17_8_13, List.forall_mem_cons.2 ⟨subd17_8_14, List.forall_mem_cons.2 ⟨subd17_8_15, List.forall_mem_cons.2 ⟨subd17_8_16, List.forall_mem_cons.2 ⟨subd17_8_17, List.forall_mem_cons.2 ⟨subd17_8_18, List.forall_mem_cons.2 ⟨subd17_8_19, List.forall_mem_cons.2 ⟨subd17_8_20, List.forall_mem_cons.2 ⟨subd17_8_21, List.forall_mem_cons.2 ⟨subd17_8_22, List.forall_mem_cons.2 ⟨subd17_8_23, List.forall_mem_cons.2 ⟨subd17_8_24, List.forall_mem_cons.2 ⟨subd17_8_25, List.forall_mem_cons.2 ⟨subd17_8_26, List.forall_mem_cons.2 ⟨subd17_8_27, List.forall_mem_cons.2 ⟨subd17_8_28, List.forall_mem_cons.2 ⟨subd17_8_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_9 : ldCheck G d17_9.U d17_9.ms ldd17_9 = true := by decide +kernel
theorem pre_okd17_9 : subPre G cell17 d17_9 = true := by decide +kernel
theorem subd17_9_0 : subd17_9 [] = true := by decide +kernel
theorem sbd17_9_0 : ∀ q ∈ blkd17_9_0, subd17_9 q = true := by
  unfold blkd17_9_0
  exact List.forall_mem_cons.2 ⟨subd17_9_0, List.forall_mem_nil _⟩
theorem ld_okd17_10 : ldCheck G d17_10.U d17_10.ms ldd17_10 = true := by decide +kernel
theorem pre_okd17_10 : subPre G cell17 d17_10 = true := by decide +kernel
theorem subd17_10_0 : subd17_10 [-2] = true := by decide +kernel
theorem subd17_10_1 : subd17_10 [-1] = true := by decide +kernel
theorem subd17_10_2 : subd17_10 [0] = true := by decide +kernel
theorem subd17_10_3 : subd17_10 [1] = true := by decide +kernel
theorem subd17_10_4 : subd17_10 [2] = true := by decide +kernel
theorem sbd17_10_0 : ∀ q ∈ blkd17_10_0, subd17_10 q = true := by
  unfold blkd17_10_0
  exact List.forall_mem_cons.2 ⟨subd17_10_0, List.forall_mem_cons.2 ⟨subd17_10_1, List.forall_mem_cons.2 ⟨subd17_10_2, List.forall_mem_cons.2 ⟨subd17_10_3, List.forall_mem_cons.2 ⟨subd17_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_11 : ldCheck G d17_11.U d17_11.ms ldd17_11 = true := by decide +kernel
theorem pre_okd17_11 : subPre G cell17 d17_11 = true := by decide +kernel
theorem subd17_11_0 : subd17_11 [] = true := by decide +kernel
theorem sbd17_11_0 : ∀ q ∈ blkd17_11_0, subd17_11 q = true := by
  unfold blkd17_11_0
  exact List.forall_mem_cons.2 ⟨subd17_11_0, List.forall_mem_nil _⟩
theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_nil _⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
