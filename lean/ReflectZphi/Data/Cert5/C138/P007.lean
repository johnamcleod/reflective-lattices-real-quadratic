import ReflectZphi.Data.Cert5.C138.Base

namespace ReflectZphi.Data.Cert5.C138

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_0 : subd9_3 [-2] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [2] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [0, 0] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [0] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C138
