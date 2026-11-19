import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_11_0 : subd10_11 [] = true := by decide +kernel
theorem sbd10_11_0 : ∀ q ∈ blkd10_11_0, subd10_11 q = true := by
  unfold blkd10_11_0
  exact List.forall_mem_cons.2 ⟨subd10_11_0, List.forall_mem_nil _⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_nil _⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_nil _⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_nil _⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_nil _⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [-3] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-2] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [-1, -4] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [-1, -3] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [-1, -2] = true := by decide +kernel
theorem subd11_4_5 : subd11_4 [-1, -1] = true := by decide +kernel
theorem subd11_4_6 : subd11_4 [-1, 0] = true := by decide +kernel
theorem subd11_4_7 : subd11_4 [-1, 1] = true := by decide +kernel
theorem subd11_4_8 : subd11_4 [-1, 2] = true := by decide +kernel
theorem subd11_4_9 : subd11_4 [0, -4] = true := by decide +kernel
theorem subd11_4_10 : subd11_4 [0, -3] = true := by decide +kernel
theorem subd11_4_11 : subd11_4 [0, -2] = true := by decide +kernel
theorem subd11_4_12 : subd11_4 [0, -1] = true := by decide +kernel
theorem subd11_4_13 : subd11_4 [0, 0] = true := by decide +kernel
theorem subd11_4_14 : subd11_4 [0, 1] = true := by decide +kernel
theorem subd11_4_15 : subd11_4 [0, 2] = true := by decide +kernel
theorem subd11_4_16 : subd11_4 [0, 3] = true := by decide +kernel
theorem subd11_4_17 : subd11_4 [1, -3] = true := by decide +kernel
theorem subd11_4_18 : subd11_4 [1, -2] = true := by decide +kernel
theorem subd11_4_19 : subd11_4 [1, -1] = true := by decide +kernel
theorem subd11_4_20 : subd11_4 [1, 0] = true := by decide +kernel
theorem subd11_4_21 : subd11_4 [1, 1] = true := by decide +kernel
theorem subd11_4_22 : subd11_4 [1, 2] = true := by decide +kernel
theorem subd11_4_23 : subd11_4 [1, 3] = true := by decide +kernel
theorem subd11_4_24 : subd11_4 [2] = true := by decide +kernel
theorem subd11_4_25 : subd11_4 [3] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_cons.2 ⟨subd11_4_5, List.forall_mem_cons.2 ⟨subd11_4_6, List.forall_mem_cons.2 ⟨subd11_4_7, List.forall_mem_cons.2 ⟨subd11_4_8, List.forall_mem_cons.2 ⟨subd11_4_9, List.forall_mem_cons.2 ⟨subd11_4_10, List.forall_mem_cons.2 ⟨subd11_4_11, List.forall_mem_cons.2 ⟨subd11_4_12, List.forall_mem_cons.2 ⟨subd11_4_13, List.forall_mem_cons.2 ⟨subd11_4_14, List.forall_mem_cons.2 ⟨subd11_4_15, List.forall_mem_cons.2 ⟨subd11_4_16, List.forall_mem_cons.2 ⟨subd11_4_17, List.forall_mem_cons.2 ⟨subd11_4_18, List.forall_mem_cons.2 ⟨subd11_4_19, List.forall_mem_cons.2 ⟨subd11_4_20, List.forall_mem_cons.2 ⟨subd11_4_21, List.forall_mem_cons.2 ⟨subd11_4_22, List.forall_mem_cons.2 ⟨subd11_4_23, List.forall_mem_cons.2 ⟨subd11_4_24, List.forall_mem_cons.2 ⟨subd11_4_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_5 : ldCheck G d11_5.U d11_5.ms ldd11_5 = true := by decide +kernel
theorem pre_okd11_5 : subPre G cell11 d11_5 = true := by decide +kernel
theorem subd11_5_0 : subd11_5 [-2] = true := by decide +kernel
theorem subd11_5_1 : subd11_5 [-1] = true := by decide +kernel
theorem subd11_5_2 : subd11_5 [0] = true := by decide +kernel
theorem subd11_5_3 : subd11_5 [1] = true := by decide +kernel
theorem subd11_5_4 : subd11_5 [2] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_cons.2 ⟨subd11_5_1, List.forall_mem_cons.2 ⟨subd11_5_2, List.forall_mem_cons.2 ⟨subd11_5_3, List.forall_mem_cons.2 ⟨subd11_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_6 : ldCheck G d11_6.U d11_6.ms ldd11_6 = true := by decide +kernel
theorem pre_okd11_6 : subPre G cell11 d11_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
