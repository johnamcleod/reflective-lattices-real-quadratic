import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-2] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-1] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [0] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [1] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [2] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-1] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [0] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [1] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [2] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-2] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-1, 2] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [-3] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-2] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [-1, -4] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [-1, -3] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [-1, -2] = true := by decide +kernel
theorem subd7_7_5 : subd7_7 [-1, -1] = true := by decide +kernel
theorem subd7_7_6 : subd7_7 [-1, 0] = true := by decide +kernel
theorem subd7_7_7 : subd7_7 [-1, 1] = true := by decide +kernel
theorem subd7_7_8 : subd7_7 [-1, 2] = true := by decide +kernel
theorem subd7_7_9 : subd7_7 [-1, 3] = true := by decide +kernel
theorem subd7_7_10 : subd7_7 [0, -4] = true := by decide +kernel
theorem subd7_7_11 : subd7_7 [0, -3] = true := by decide +kernel
theorem subd7_7_12 : subd7_7 [0, -2] = true := by decide +kernel
theorem subd7_7_13 : subd7_7 [0, -1] = true := by decide +kernel
theorem subd7_7_14 : subd7_7 [0, 0] = true := by decide +kernel
theorem subd7_7_15 : subd7_7 [0, 1] = true := by decide +kernel
theorem subd7_7_16 : subd7_7 [0, 2] = true := by decide +kernel
theorem subd7_7_17 : subd7_7 [0, 3] = true := by decide +kernel
theorem subd7_7_18 : subd7_7 [1, -4] = true := by decide +kernel
theorem subd7_7_19 : subd7_7 [1, -3] = true := by decide +kernel
theorem subd7_7_20 : subd7_7 [1, -2] = true := by decide +kernel
theorem subd7_7_21 : subd7_7 [1, -1] = true := by decide +kernel
theorem subd7_7_22 : subd7_7 [1, 0] = true := by decide +kernel
theorem subd7_7_23 : subd7_7 [1, 1] = true := by decide +kernel
theorem subd7_7_24 : subd7_7 [1, 2] = true := by decide +kernel
theorem subd7_7_25 : subd7_7 [1, 3] = true := by decide +kernel
theorem subd7_7_26 : subd7_7 [2] = true := by decide +kernel
theorem subd7_7_27 : subd7_7 [3] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_cons.2 ⟨subd7_7_5, List.forall_mem_cons.2 ⟨subd7_7_6, List.forall_mem_cons.2 ⟨subd7_7_7, List.forall_mem_cons.2 ⟨subd7_7_8, List.forall_mem_cons.2 ⟨subd7_7_9, List.forall_mem_cons.2 ⟨subd7_7_10, List.forall_mem_cons.2 ⟨subd7_7_11, List.forall_mem_cons.2 ⟨subd7_7_12, List.forall_mem_cons.2 ⟨subd7_7_13, List.forall_mem_cons.2 ⟨subd7_7_14, List.forall_mem_cons.2 ⟨subd7_7_15, List.forall_mem_cons.2 ⟨subd7_7_16, List.forall_mem_cons.2 ⟨subd7_7_17, List.forall_mem_cons.2 ⟨subd7_7_18, List.forall_mem_cons.2 ⟨subd7_7_19, List.forall_mem_cons.2 ⟨subd7_7_20, List.forall_mem_cons.2 ⟨subd7_7_21, List.forall_mem_cons.2 ⟨subd7_7_22, List.forall_mem_cons.2 ⟨subd7_7_23, List.forall_mem_cons.2 ⟨subd7_7_24, List.forall_mem_cons.2 ⟨subd7_7_25, List.forall_mem_cons.2 ⟨subd7_7_26, List.forall_mem_cons.2 ⟨subd7_7_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [0] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-1] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [0] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [1] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
