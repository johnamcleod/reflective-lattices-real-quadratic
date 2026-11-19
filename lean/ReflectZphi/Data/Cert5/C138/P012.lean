import ReflectZphi.Data.Cert5.C138.Base

namespace ReflectZphi.Data.Cert5.C138

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel
theorem subd16_2_0 : subd16_2 [-2] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [-1] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [0] = true := by decide +kernel
theorem subd16_2_3 : subd16_2 [1] = true := by decide +kernel
theorem subd16_2_4 : subd16_2 [2] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_cons.2 ⟨subd16_2_3, List.forall_mem_cons.2 ⟨subd16_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [-2] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [-1, -3] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [-1, -2] = true := by decide +kernel
theorem subd16_3_3 : subd16_3 [-1, -1] = true := by decide +kernel
theorem subd16_3_4 : subd16_3 [-1, 0] = true := by decide +kernel
theorem subd16_3_5 : subd16_3 [-1, 1] = true := by decide +kernel
theorem subd16_3_6 : subd16_3 [-1, 2] = true := by decide +kernel
theorem subd16_3_7 : subd16_3 [0, -3] = true := by decide +kernel
theorem subd16_3_8 : subd16_3 [0, -2] = true := by decide +kernel
theorem subd16_3_9 : subd16_3 [0, -1] = true := by decide +kernel
theorem subd16_3_10 : subd16_3 [0, 0] = true := by decide +kernel
theorem subd16_3_11 : subd16_3 [0, 1] = true := by decide +kernel
theorem subd16_3_12 : subd16_3 [0, 2] = true := by decide +kernel
theorem subd16_3_13 : subd16_3 [1, -3] = true := by decide +kernel
theorem subd16_3_14 : subd16_3 [1, -2] = true := by decide +kernel
theorem subd16_3_15 : subd16_3 [1, -1] = true := by decide +kernel
theorem subd16_3_16 : subd16_3 [1, 0] = true := by decide +kernel
theorem subd16_3_17 : subd16_3 [1, 1] = true := by decide +kernel
theorem subd16_3_18 : subd16_3 [1, 2] = true := by decide +kernel
theorem subd16_3_19 : subd16_3 [2] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_cons.2 ⟨subd16_3_3, List.forall_mem_cons.2 ⟨subd16_3_4, List.forall_mem_cons.2 ⟨subd16_3_5, List.forall_mem_cons.2 ⟨subd16_3_6, List.forall_mem_cons.2 ⟨subd16_3_7, List.forall_mem_cons.2 ⟨subd16_3_8, List.forall_mem_cons.2 ⟨subd16_3_9, List.forall_mem_cons.2 ⟨subd16_3_10, List.forall_mem_cons.2 ⟨subd16_3_11, List.forall_mem_cons.2 ⟨subd16_3_12, List.forall_mem_cons.2 ⟨subd16_3_13, List.forall_mem_cons.2 ⟨subd16_3_14, List.forall_mem_cons.2 ⟨subd16_3_15, List.forall_mem_cons.2 ⟨subd16_3_16, List.forall_mem_cons.2 ⟨subd16_3_17, List.forall_mem_cons.2 ⟨subd16_3_18, List.forall_mem_cons.2 ⟨subd16_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_nil _⟩
theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [-3] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-2] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [-1, -4] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [-1, -3] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [-1, -2] = true := by decide +kernel
theorem subd17_1_5 : subd17_1 [-1, -1] = true := by decide +kernel
theorem subd17_1_6 : subd17_1 [-1, 0] = true := by decide +kernel
theorem subd17_1_7 : subd17_1 [-1, 1] = true := by decide +kernel
theorem subd17_1_8 : subd17_1 [-1, 2] = true := by decide +kernel
theorem subd17_1_9 : subd17_1 [0, -4] = true := by decide +kernel
theorem subd17_1_10 : subd17_1 [0, -3] = true := by decide +kernel
theorem subd17_1_11 : subd17_1 [0, -2] = true := by decide +kernel
theorem subd17_1_12 : subd17_1 [0, -1] = true := by decide +kernel
theorem subd17_1_13 : subd17_1 [0, 0] = true := by decide +kernel
theorem subd17_1_14 : subd17_1 [0, 1] = true := by decide +kernel
theorem subd17_1_15 : subd17_1 [0, 2] = true := by decide +kernel
theorem subd17_1_16 : subd17_1 [0, 3] = true := by decide +kernel
theorem subd17_1_17 : subd17_1 [1, -3] = true := by decide +kernel
theorem subd17_1_18 : subd17_1 [1, -2] = true := by decide +kernel
theorem subd17_1_19 : subd17_1 [1, -1] = true := by decide +kernel
theorem subd17_1_20 : subd17_1 [1, 0] = true := by decide +kernel
theorem subd17_1_21 : subd17_1 [1, 1] = true := by decide +kernel
theorem subd17_1_22 : subd17_1 [1, 2] = true := by decide +kernel
theorem subd17_1_23 : subd17_1 [1, 3] = true := by decide +kernel
theorem subd17_1_24 : subd17_1 [2] = true := by decide +kernel
theorem subd17_1_25 : subd17_1 [3] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_cons.2 ⟨subd17_1_5, List.forall_mem_cons.2 ⟨subd17_1_6, List.forall_mem_cons.2 ⟨subd17_1_7, List.forall_mem_cons.2 ⟨subd17_1_8, List.forall_mem_cons.2 ⟨subd17_1_9, List.forall_mem_cons.2 ⟨subd17_1_10, List.forall_mem_cons.2 ⟨subd17_1_11, List.forall_mem_cons.2 ⟨subd17_1_12, List.forall_mem_cons.2 ⟨subd17_1_13, List.forall_mem_cons.2 ⟨subd17_1_14, List.forall_mem_cons.2 ⟨subd17_1_15, List.forall_mem_cons.2 ⟨subd17_1_16, List.forall_mem_cons.2 ⟨subd17_1_17, List.forall_mem_cons.2 ⟨subd17_1_18, List.forall_mem_cons.2 ⟨subd17_1_19, List.forall_mem_cons.2 ⟨subd17_1_20, List.forall_mem_cons.2 ⟨subd17_1_21, List.forall_mem_cons.2 ⟨subd17_1_22, List.forall_mem_cons.2 ⟨subd17_1_23, List.forall_mem_cons.2 ⟨subd17_1_24, List.forall_mem_cons.2 ⟨subd17_1_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel
theorem subd17_2_0 : subd17_2 [] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_nil _⟩
theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [-2] = true := by decide +kernel
theorem subd17_3_1 : subd17_3 [-1] = true := by decide +kernel
theorem subd17_3_2 : subd17_3 [0] = true := by decide +kernel
theorem subd17_3_3 : subd17_3 [1] = true := by decide +kernel
theorem subd17_3_4 : subd17_3 [2] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_cons.2 ⟨subd17_3_1, List.forall_mem_cons.2 ⟨subd17_3_2, List.forall_mem_cons.2 ⟨subd17_3_3, List.forall_mem_cons.2 ⟨subd17_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C138
