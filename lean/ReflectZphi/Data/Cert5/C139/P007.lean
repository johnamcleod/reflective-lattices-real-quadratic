import ReflectZphi.Data.Cert5.C139.Base

namespace ReflectZphi.Data.Cert5.C139

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-1] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [0, 0, -8] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, 0, 7] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [1] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-1] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [0] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [1, 2] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_nil _⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-1, -1] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [2] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C139
