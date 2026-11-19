import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_9 : ldCheck G d9_9.U d9_9.ms ldd9_9 = true := by decide +kernel
theorem pre_okd9_9 : subPre G cell9 d9_9 = true := by decide +kernel
theorem subd9_9_0 : subd9_9 [] = true := by decide +kernel
theorem sbd9_9_0 : ∀ q ∈ blkd9_9_0, subd9_9 q = true := by
  unfold blkd9_9_0
  exact List.forall_mem_cons.2 ⟨subd9_9_0, List.forall_mem_nil _⟩
theorem ld_okd9_10 : ldCheck G d9_10.U d9_10.ms ldd9_10 = true := by decide +kernel
theorem pre_okd9_10 : subPre G cell9 d9_10 = true := by decide +kernel
theorem subd9_10_0 : subd9_10 [-2] = true := by decide +kernel
theorem subd9_10_1 : subd9_10 [-1] = true := by decide +kernel
theorem subd9_10_2 : subd9_10 [0] = true := by decide +kernel
theorem subd9_10_3 : subd9_10 [1] = true := by decide +kernel
theorem subd9_10_4 : subd9_10 [2] = true := by decide +kernel
theorem sbd9_10_0 : ∀ q ∈ blkd9_10_0, subd9_10 q = true := by
  unfold blkd9_10_0
  exact List.forall_mem_cons.2 ⟨subd9_10_0, List.forall_mem_cons.2 ⟨subd9_10_1, List.forall_mem_cons.2 ⟨subd9_10_2, List.forall_mem_cons.2 ⟨subd9_10_3, List.forall_mem_cons.2 ⟨subd9_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_11 : ldCheck G d9_11.U d9_11.ms ldd9_11 = true := by decide +kernel
theorem pre_okd9_11 : subPre G cell9 d9_11 = true := by decide +kernel
theorem subd9_11_0 : subd9_11 [] = true := by decide +kernel
theorem sbd9_11_0 : ∀ q ∈ blkd9_11_0, subd9_11 q = true := by
  unfold blkd9_11_0
  exact List.forall_mem_cons.2 ⟨subd9_11_0, List.forall_mem_nil _⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_nil _⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_nil _⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-2] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [1, 1] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [2] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
