import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_nil _⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_nil _⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_nil _⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-3] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-2] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-1] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [1] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [2] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [3] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-3] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [2, -2] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [2, -1] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [3] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-2, -2] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-2, -1] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [-2, 0] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [-2, 1] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [-1, -3] = true := by decide +kernel
theorem subd9_4_5 : subd9_4 [-1, -2] = true := by decide +kernel
theorem subd9_4_6 : subd9_4 [-1, -1, -7] = true := by decide +kernel
theorem subd9_4_7 : subd9_4 [-1, -1, -6] = true := by decide +kernel
theorem subd9_4_8 : subd9_4 [-1, -1, -5] = true := by decide +kernel
theorem subd9_4_9 : subd9_4 [-1, -1, -4] = true := by decide +kernel
theorem subd9_4_10 : subd9_4 [-1, -1, -3] = true := by decide +kernel
theorem subd9_4_11 : subd9_4 [-1, -1, -2] = true := by decide +kernel
theorem subd9_4_12 : subd9_4 [-1, -1, -1] = true := by decide +kernel
theorem subd9_4_13 : subd9_4 [-1, -1, 0] = true := by decide +kernel
theorem subd9_4_14 : subd9_4 [-1, -1, 1] = true := by decide +kernel
theorem subd9_4_15 : subd9_4 [-1, -1, 2] = true := by decide +kernel
theorem subd9_4_16 : subd9_4 [-1, -1, 3] = true := by decide +kernel
theorem subd9_4_17 : subd9_4 [-1, -1, 4] = true := by decide +kernel
theorem subd9_4_18 : subd9_4 [-1, -1, 5] = true := by decide +kernel
theorem subd9_4_19 : subd9_4 [-1, -1, 6] = true := by decide +kernel
theorem subd9_4_20 : subd9_4 [-1, -1, 7] = true := by decide +kernel
theorem subd9_4_21 : subd9_4 [-1, 0, -8] = true := by decide +kernel
theorem subd9_4_22 : subd9_4 [-1, 0, -7] = true := by decide +kernel
theorem subd9_4_23 : subd9_4 [-1, 0, -6] = true := by decide +kernel
theorem subd9_4_24 : subd9_4 [-1, 0, -5] = true := by decide +kernel
theorem subd9_4_25 : subd9_4 [-1, 0, -4] = true := by decide +kernel
theorem subd9_4_26 : subd9_4 [-1, 0, -3] = true := by decide +kernel
theorem subd9_4_27 : subd9_4 [-1, 0, -2] = true := by decide +kernel
theorem subd9_4_28 : subd9_4 [-1, 0, -1] = true := by decide +kernel
theorem subd9_4_29 : subd9_4 [-1, 0, 0] = true := by decide +kernel
theorem subd9_4_30 : subd9_4 [-1, 0, 1] = true := by decide +kernel
theorem subd9_4_31 : subd9_4 [-1, 0, 2] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_cons.2 ⟨subd9_4_5, List.forall_mem_cons.2 ⟨subd9_4_6, List.forall_mem_cons.2 ⟨subd9_4_7, List.forall_mem_cons.2 ⟨subd9_4_8, List.forall_mem_cons.2 ⟨subd9_4_9, List.forall_mem_cons.2 ⟨subd9_4_10, List.forall_mem_cons.2 ⟨subd9_4_11, List.forall_mem_cons.2 ⟨subd9_4_12, List.forall_mem_cons.2 ⟨subd9_4_13, List.forall_mem_cons.2 ⟨subd9_4_14, List.forall_mem_cons.2 ⟨subd9_4_15, List.forall_mem_cons.2 ⟨subd9_4_16, List.forall_mem_cons.2 ⟨subd9_4_17, List.forall_mem_cons.2 ⟨subd9_4_18, List.forall_mem_cons.2 ⟨subd9_4_19, List.forall_mem_cons.2 ⟨subd9_4_20, List.forall_mem_cons.2 ⟨subd9_4_21, List.forall_mem_cons.2 ⟨subd9_4_22, List.forall_mem_cons.2 ⟨subd9_4_23, List.forall_mem_cons.2 ⟨subd9_4_24, List.forall_mem_cons.2 ⟨subd9_4_25, List.forall_mem_cons.2 ⟨subd9_4_26, List.forall_mem_cons.2 ⟨subd9_4_27, List.forall_mem_cons.2 ⟨subd9_4_28, List.forall_mem_cons.2 ⟨subd9_4_29, List.forall_mem_cons.2 ⟨subd9_4_30, List.forall_mem_cons.2 ⟨subd9_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C122
