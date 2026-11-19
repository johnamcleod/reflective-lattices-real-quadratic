import ReflectZphi.Data.Cert5.C117.Base

namespace ReflectZphi.Data.Cert5.C117

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-1] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [0] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [1] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-3] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-1, -2] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-1, -1] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-1, 0] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-1, 1] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-1, 2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [2] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [3] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-1] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [0] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [1] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_nil _⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [0] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [1] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C117
