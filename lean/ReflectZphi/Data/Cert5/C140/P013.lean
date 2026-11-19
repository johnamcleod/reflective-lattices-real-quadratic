import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-2, -2] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-2, -1] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-2, 0] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-2, 1] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [1, 1] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [2, 1] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-2] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [0] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [1] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [2] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [0] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [0] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [1] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
