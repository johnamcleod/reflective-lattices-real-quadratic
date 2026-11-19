import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_6_0 : subd9_6 [-2] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-1] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [0] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [1] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [2] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-1] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [0] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [1] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-3] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-1, -4] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [0, 3] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [2] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [3] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [0, 0] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-1, -2] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-1, -1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-1, 0] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-1, 1] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C132
