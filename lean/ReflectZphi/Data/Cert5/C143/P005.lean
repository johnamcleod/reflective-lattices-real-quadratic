import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_0 : subd8_0 [-3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [2] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [3] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-3] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-1, 3] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, -4] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [0, 3] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [1, -4] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [1, 2] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [2] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [3] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-2] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-1, -5] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [2] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [3] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-2] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [2] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
