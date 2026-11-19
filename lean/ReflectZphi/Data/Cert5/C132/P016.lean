import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_5 : ldCheck G d11_5.U d11_5.ms ldd11_5 = true := by decide +kernel
theorem pre_okd11_5 : subPre G cell11 d11_5 = true := by decide +kernel
theorem subd11_5_0 : subd11_5 [] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_nil _⟩
theorem ld_okd11_6 : ldCheck G d11_6.U d11_6.ms ldd11_6 = true := by decide +kernel
theorem pre_okd11_6 : subPre G cell11 d11_6 = true := by decide +kernel
theorem subd11_6_0 : subd11_6 [-3] = true := by decide +kernel
theorem subd11_6_1 : subd11_6 [-2] = true := by decide +kernel
theorem subd11_6_2 : subd11_6 [-1, -3] = true := by decide +kernel
theorem subd11_6_3 : subd11_6 [-1, -2] = true := by decide +kernel
theorem subd11_6_4 : subd11_6 [-1, -1] = true := by decide +kernel
theorem subd11_6_5 : subd11_6 [-1, 0] = true := by decide +kernel
theorem subd11_6_6 : subd11_6 [-1, 1] = true := by decide +kernel
theorem subd11_6_7 : subd11_6 [-1, 2] = true := by decide +kernel
theorem subd11_6_8 : subd11_6 [-1, 3] = true := by decide +kernel
theorem subd11_6_9 : subd11_6 [0, -4] = true := by decide +kernel
theorem subd11_6_10 : subd11_6 [0, -3] = true := by decide +kernel
theorem subd11_6_11 : subd11_6 [0, -2] = true := by decide +kernel
theorem subd11_6_12 : subd11_6 [0, -1] = true := by decide +kernel
theorem subd11_6_13 : subd11_6 [0, 0] = true := by decide +kernel
theorem subd11_6_14 : subd11_6 [0, 1] = true := by decide +kernel
theorem subd11_6_15 : subd11_6 [0, 2] = true := by decide +kernel
theorem subd11_6_16 : subd11_6 [0, 3] = true := by decide +kernel
theorem subd11_6_17 : subd11_6 [1, -4] = true := by decide +kernel
theorem subd11_6_18 : subd11_6 [1, -3] = true := by decide +kernel
theorem subd11_6_19 : subd11_6 [1, -2] = true := by decide +kernel
theorem subd11_6_20 : subd11_6 [1, -1] = true := by decide +kernel
theorem subd11_6_21 : subd11_6 [1, 0] = true := by decide +kernel
theorem subd11_6_22 : subd11_6 [1, 1] = true := by decide +kernel
theorem subd11_6_23 : subd11_6 [1, 2] = true := by decide +kernel
theorem subd11_6_24 : subd11_6 [2] = true := by decide +kernel
theorem subd11_6_25 : subd11_6 [3] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_cons.2 ⟨subd11_6_1, List.forall_mem_cons.2 ⟨subd11_6_2, List.forall_mem_cons.2 ⟨subd11_6_3, List.forall_mem_cons.2 ⟨subd11_6_4, List.forall_mem_cons.2 ⟨subd11_6_5, List.forall_mem_cons.2 ⟨subd11_6_6, List.forall_mem_cons.2 ⟨subd11_6_7, List.forall_mem_cons.2 ⟨subd11_6_8, List.forall_mem_cons.2 ⟨subd11_6_9, List.forall_mem_cons.2 ⟨subd11_6_10, List.forall_mem_cons.2 ⟨subd11_6_11, List.forall_mem_cons.2 ⟨subd11_6_12, List.forall_mem_cons.2 ⟨subd11_6_13, List.forall_mem_cons.2 ⟨subd11_6_14, List.forall_mem_cons.2 ⟨subd11_6_15, List.forall_mem_cons.2 ⟨subd11_6_16, List.forall_mem_cons.2 ⟨subd11_6_17, List.forall_mem_cons.2 ⟨subd11_6_18, List.forall_mem_cons.2 ⟨subd11_6_19, List.forall_mem_cons.2 ⟨subd11_6_20, List.forall_mem_cons.2 ⟨subd11_6_21, List.forall_mem_cons.2 ⟨subd11_6_22, List.forall_mem_cons.2 ⟨subd11_6_23, List.forall_mem_cons.2 ⟨subd11_6_24, List.forall_mem_cons.2 ⟨subd11_6_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_7 : ldCheck G d11_7.U d11_7.ms ldd11_7 = true := by decide +kernel
theorem pre_okd11_7 : subPre G cell11 d11_7 = true := by decide +kernel
theorem subd11_7_0 : subd11_7 [-1] = true := by decide +kernel
theorem subd11_7_1 : subd11_7 [0, -2] = true := by decide +kernel
theorem subd11_7_2 : subd11_7 [0, -1] = true := by decide +kernel
theorem subd11_7_3 : subd11_7 [0, 0] = true := by decide +kernel
theorem subd11_7_4 : subd11_7 [0, 1] = true := by decide +kernel
theorem subd11_7_5 : subd11_7 [1] = true := by decide +kernel
theorem sbd11_7_0 : ∀ q ∈ blkd11_7_0, subd11_7 q = true := by
  unfold blkd11_7_0
  exact List.forall_mem_cons.2 ⟨subd11_7_0, List.forall_mem_cons.2 ⟨subd11_7_1, List.forall_mem_cons.2 ⟨subd11_7_2, List.forall_mem_cons.2 ⟨subd11_7_3, List.forall_mem_cons.2 ⟨subd11_7_4, List.forall_mem_cons.2 ⟨subd11_7_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-2] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-1] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [0] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [2] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [0] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [1] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [2] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-2] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-1] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [0] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [1] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [2] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
