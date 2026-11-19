import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_5_0 : subd7_5 [-3] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-1, -4] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-1, -3] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-1, -2] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [-1, -1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [-1, 0] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [-1, 1] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [-1, 2] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [-1, 3] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [0, -4] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [0, -3] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_14 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_15 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_16 : subd7_5 [0, 2] = true := by decide +kernel
theorem subd7_5_17 : subd7_5 [0, 3] = true := by decide +kernel
theorem subd7_5_18 : subd7_5 [1, -4] = true := by decide +kernel
theorem subd7_5_19 : subd7_5 [1, -3] = true := by decide +kernel
theorem subd7_5_20 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_21 : subd7_5 [1, -1] = true := by decide +kernel
theorem subd7_5_22 : subd7_5 [1, 0] = true := by decide +kernel
theorem subd7_5_23 : subd7_5 [1, 1] = true := by decide +kernel
theorem subd7_5_24 : subd7_5 [1, 2] = true := by decide +kernel
theorem subd7_5_25 : subd7_5 [1, 3] = true := by decide +kernel
theorem subd7_5_26 : subd7_5 [2] = true := by decide +kernel
theorem subd7_5_27 : subd7_5 [3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_cons.2 ⟨subd7_5_14, List.forall_mem_cons.2 ⟨subd7_5_15, List.forall_mem_cons.2 ⟨subd7_5_16, List.forall_mem_cons.2 ⟨subd7_5_17, List.forall_mem_cons.2 ⟨subd7_5_18, List.forall_mem_cons.2 ⟨subd7_5_19, List.forall_mem_cons.2 ⟨subd7_5_20, List.forall_mem_cons.2 ⟨subd7_5_21, List.forall_mem_cons.2 ⟨subd7_5_22, List.forall_mem_cons.2 ⟨subd7_5_23, List.forall_mem_cons.2 ⟨subd7_5_24, List.forall_mem_cons.2 ⟨subd7_5_25, List.forall_mem_cons.2 ⟨subd7_5_26, List.forall_mem_cons.2 ⟨subd7_5_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_nil _⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_nil _⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_nil _⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_nil _⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
