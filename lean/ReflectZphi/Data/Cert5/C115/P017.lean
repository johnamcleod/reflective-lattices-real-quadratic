import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_6_0 : subd11_6 [-2] = true := by decide +kernel
theorem subd11_6_1 : subd11_6 [-1, -3] = true := by decide +kernel
theorem subd11_6_2 : subd11_6 [-1, -2] = true := by decide +kernel
theorem subd11_6_3 : subd11_6 [-1, -1] = true := by decide +kernel
theorem subd11_6_4 : subd11_6 [-1, 0] = true := by decide +kernel
theorem subd11_6_5 : subd11_6 [-1, 1] = true := by decide +kernel
theorem subd11_6_6 : subd11_6 [-1, 2] = true := by decide +kernel
theorem subd11_6_7 : subd11_6 [0, -3] = true := by decide +kernel
theorem subd11_6_8 : subd11_6 [0, -2] = true := by decide +kernel
theorem subd11_6_9 : subd11_6 [0, -1] = true := by decide +kernel
theorem subd11_6_10 : subd11_6 [0, 0] = true := by decide +kernel
theorem subd11_6_11 : subd11_6 [0, 1] = true := by decide +kernel
theorem subd11_6_12 : subd11_6 [0, 2] = true := by decide +kernel
theorem subd11_6_13 : subd11_6 [1, -3] = true := by decide +kernel
theorem subd11_6_14 : subd11_6 [1, -2] = true := by decide +kernel
theorem subd11_6_15 : subd11_6 [1, -1] = true := by decide +kernel
theorem subd11_6_16 : subd11_6 [1, 0] = true := by decide +kernel
theorem subd11_6_17 : subd11_6 [1, 1] = true := by decide +kernel
theorem subd11_6_18 : subd11_6 [1, 2] = true := by decide +kernel
theorem subd11_6_19 : subd11_6 [2] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_cons.2 ⟨subd11_6_1, List.forall_mem_cons.2 ⟨subd11_6_2, List.forall_mem_cons.2 ⟨subd11_6_3, List.forall_mem_cons.2 ⟨subd11_6_4, List.forall_mem_cons.2 ⟨subd11_6_5, List.forall_mem_cons.2 ⟨subd11_6_6, List.forall_mem_cons.2 ⟨subd11_6_7, List.forall_mem_cons.2 ⟨subd11_6_8, List.forall_mem_cons.2 ⟨subd11_6_9, List.forall_mem_cons.2 ⟨subd11_6_10, List.forall_mem_cons.2 ⟨subd11_6_11, List.forall_mem_cons.2 ⟨subd11_6_12, List.forall_mem_cons.2 ⟨subd11_6_13, List.forall_mem_cons.2 ⟨subd11_6_14, List.forall_mem_cons.2 ⟨subd11_6_15, List.forall_mem_cons.2 ⟨subd11_6_16, List.forall_mem_cons.2 ⟨subd11_6_17, List.forall_mem_cons.2 ⟨subd11_6_18, List.forall_mem_cons.2 ⟨subd11_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_7 : ldCheck G d11_7.U d11_7.ms ldd11_7 = true := by decide +kernel
theorem pre_okd11_7 : subPre G cell11 d11_7 = true := by decide +kernel
theorem subd11_7_0 : subd11_7 [-2] = true := by decide +kernel
theorem subd11_7_1 : subd11_7 [-1] = true := by decide +kernel
theorem subd11_7_2 : subd11_7 [0] = true := by decide +kernel
theorem subd11_7_3 : subd11_7 [1] = true := by decide +kernel
theorem subd11_7_4 : subd11_7 [2] = true := by decide +kernel
theorem sbd11_7_0 : ∀ q ∈ blkd11_7_0, subd11_7 q = true := by
  unfold blkd11_7_0
  exact List.forall_mem_cons.2 ⟨subd11_7_0, List.forall_mem_cons.2 ⟨subd11_7_1, List.forall_mem_cons.2 ⟨subd11_7_2, List.forall_mem_cons.2 ⟨subd11_7_3, List.forall_mem_cons.2 ⟨subd11_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_8 : ldCheck G d11_8.U d11_8.ms ldd11_8 = true := by decide +kernel
theorem pre_okd11_8 : subPre G cell11 d11_8 = true := by decide +kernel
theorem subd11_8_0 : subd11_8 [-2] = true := by decide +kernel
theorem subd11_8_1 : subd11_8 [-1, -3] = true := by decide +kernel
theorem subd11_8_2 : subd11_8 [-1, -2] = true := by decide +kernel
theorem subd11_8_3 : subd11_8 [-1, -1] = true := by decide +kernel
theorem subd11_8_4 : subd11_8 [-1, 0] = true := by decide +kernel
theorem subd11_8_5 : subd11_8 [-1, 1] = true := by decide +kernel
theorem subd11_8_6 : subd11_8 [-1, 2] = true := by decide +kernel
theorem subd11_8_7 : subd11_8 [-1, 3] = true := by decide +kernel
theorem subd11_8_8 : subd11_8 [0, -4] = true := by decide +kernel
theorem subd11_8_9 : subd11_8 [0, -3] = true := by decide +kernel
theorem subd11_8_10 : subd11_8 [0, -2] = true := by decide +kernel
theorem subd11_8_11 : subd11_8 [0, -1] = true := by decide +kernel
theorem subd11_8_12 : subd11_8 [0, 0] = true := by decide +kernel
theorem subd11_8_13 : subd11_8 [0, 1] = true := by decide +kernel
theorem subd11_8_14 : subd11_8 [0, 2] = true := by decide +kernel
theorem subd11_8_15 : subd11_8 [0, 3] = true := by decide +kernel
theorem subd11_8_16 : subd11_8 [1, -4] = true := by decide +kernel
theorem subd11_8_17 : subd11_8 [1, -3] = true := by decide +kernel
theorem subd11_8_18 : subd11_8 [1, -2] = true := by decide +kernel
theorem subd11_8_19 : subd11_8 [1, -1] = true := by decide +kernel
theorem subd11_8_20 : subd11_8 [1, 0] = true := by decide +kernel
theorem subd11_8_21 : subd11_8 [1, 1] = true := by decide +kernel
theorem subd11_8_22 : subd11_8 [1, 2] = true := by decide +kernel
theorem subd11_8_23 : subd11_8 [2] = true := by decide +kernel
theorem sbd11_8_0 : ∀ q ∈ blkd11_8_0, subd11_8 q = true := by
  unfold blkd11_8_0
  exact List.forall_mem_cons.2 ⟨subd11_8_0, List.forall_mem_cons.2 ⟨subd11_8_1, List.forall_mem_cons.2 ⟨subd11_8_2, List.forall_mem_cons.2 ⟨subd11_8_3, List.forall_mem_cons.2 ⟨subd11_8_4, List.forall_mem_cons.2 ⟨subd11_8_5, List.forall_mem_cons.2 ⟨subd11_8_6, List.forall_mem_cons.2 ⟨subd11_8_7, List.forall_mem_cons.2 ⟨subd11_8_8, List.forall_mem_cons.2 ⟨subd11_8_9, List.forall_mem_cons.2 ⟨subd11_8_10, List.forall_mem_cons.2 ⟨subd11_8_11, List.forall_mem_cons.2 ⟨subd11_8_12, List.forall_mem_cons.2 ⟨subd11_8_13, List.forall_mem_cons.2 ⟨subd11_8_14, List.forall_mem_cons.2 ⟨subd11_8_15, List.forall_mem_cons.2 ⟨subd11_8_16, List.forall_mem_cons.2 ⟨subd11_8_17, List.forall_mem_cons.2 ⟨subd11_8_18, List.forall_mem_cons.2 ⟨subd11_8_19, List.forall_mem_cons.2 ⟨subd11_8_20, List.forall_mem_cons.2 ⟨subd11_8_21, List.forall_mem_cons.2 ⟨subd11_8_22, List.forall_mem_cons.2 ⟨subd11_8_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_9 : ldCheck G d11_9.U d11_9.ms ldd11_9 = true := by decide +kernel
theorem pre_okd11_9 : subPre G cell11 d11_9 = true := by decide +kernel
theorem subd11_9_0 : subd11_9 [] = true := by decide +kernel
theorem sbd11_9_0 : ∀ q ∈ blkd11_9_0, subd11_9 q = true := by
  unfold blkd11_9_0
  exact List.forall_mem_cons.2 ⟨subd11_9_0, List.forall_mem_nil _⟩
theorem ld_okd11_10 : ldCheck G d11_10.U d11_10.ms ldd11_10 = true := by decide +kernel
theorem pre_okd11_10 : subPre G cell11 d11_10 = true := by decide +kernel
theorem subd11_10_0 : subd11_10 [-2] = true := by decide +kernel
theorem subd11_10_1 : subd11_10 [-1] = true := by decide +kernel
theorem subd11_10_2 : subd11_10 [0] = true := by decide +kernel
theorem subd11_10_3 : subd11_10 [1] = true := by decide +kernel
theorem subd11_10_4 : subd11_10 [2] = true := by decide +kernel
theorem sbd11_10_0 : ∀ q ∈ blkd11_10_0, subd11_10 q = true := by
  unfold blkd11_10_0
  exact List.forall_mem_cons.2 ⟨subd11_10_0, List.forall_mem_cons.2 ⟨subd11_10_1, List.forall_mem_cons.2 ⟨subd11_10_2, List.forall_mem_cons.2 ⟨subd11_10_3, List.forall_mem_cons.2 ⟨subd11_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_11 : ldCheck G d11_11.U d11_11.ms ldd11_11 = true := by decide +kernel
theorem pre_okd11_11 : subPre G cell11 d11_11 = true := by decide +kernel
theorem subd11_11_0 : subd11_11 [] = true := by decide +kernel
theorem sbd11_11_0 : ∀ q ∈ blkd11_11_0, subd11_11 q = true := by
  unfold blkd11_11_0
  exact List.forall_mem_cons.2 ⟨subd11_11_0, List.forall_mem_nil _⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
