import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_0 : subd9_0 [-2] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [0] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [1] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [2] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-3] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-1] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [0] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [1] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [2] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [3] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-2] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-1] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [0] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [1] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [2] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-2] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-1] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [0] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [1] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [2] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-1] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [0] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [1] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-1] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [0] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [1] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [2] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [-4] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-3] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-2, -4] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-2, -3] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-2, -2] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-2, -1] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [-2, 0] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [-2, 1] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [-2, 2] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [-2, 3] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [-1, -5] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [-1, -4] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [-1, -3] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [-1, -2] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [-1, -1] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [-1, 0] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [-1, 1] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [-1, 2] = true := by decide +kernel
theorem subd9_6_18 : subd9_6 [-1, 3] = true := by decide +kernel
theorem subd9_6_19 : subd9_6 [-1, 4] = true := by decide +kernel
theorem subd9_6_20 : subd9_6 [0, -5] = true := by decide +kernel
theorem subd9_6_21 : subd9_6 [0, -4] = true := by decide +kernel
theorem subd9_6_22 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_23 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_24 : subd9_6 [0, -1] = true := by decide +kernel
theorem subd9_6_25 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_26 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_27 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_28 : subd9_6 [0, 3] = true := by decide +kernel
theorem subd9_6_29 : subd9_6 [0, 4] = true := by decide +kernel
theorem subd9_6_30 : subd9_6 [1, -5] = true := by decide +kernel
theorem subd9_6_31 : subd9_6 [1, -4] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_cons.2 ⟨subd9_6_18, List.forall_mem_cons.2 ⟨subd9_6_19, List.forall_mem_cons.2 ⟨subd9_6_20, List.forall_mem_cons.2 ⟨subd9_6_21, List.forall_mem_cons.2 ⟨subd9_6_22, List.forall_mem_cons.2 ⟨subd9_6_23, List.forall_mem_cons.2 ⟨subd9_6_24, List.forall_mem_cons.2 ⟨subd9_6_25, List.forall_mem_cons.2 ⟨subd9_6_26, List.forall_mem_cons.2 ⟨subd9_6_27, List.forall_mem_cons.2 ⟨subd9_6_28, List.forall_mem_cons.2 ⟨subd9_6_29, List.forall_mem_cons.2 ⟨subd9_6_30, List.forall_mem_cons.2 ⟨subd9_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
