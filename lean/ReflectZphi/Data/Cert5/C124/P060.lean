import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_14_0 : subd11_14 [-3] = true := by decide +kernel
theorem subd11_14_1 : subd11_14 [-2] = true := by decide +kernel
theorem subd11_14_2 : subd11_14 [-1, -4] = true := by decide +kernel
theorem subd11_14_3 : subd11_14 [-1, -3] = true := by decide +kernel
theorem subd11_14_4 : subd11_14 [-1, -2] = true := by decide +kernel
theorem subd11_14_5 : subd11_14 [-1, -1] = true := by decide +kernel
theorem subd11_14_6 : subd11_14 [-1, 0] = true := by decide +kernel
theorem subd11_14_7 : subd11_14 [-1, 1] = true := by decide +kernel
theorem subd11_14_8 : subd11_14 [-1, 2] = true := by decide +kernel
theorem subd11_14_9 : subd11_14 [-1, 3] = true := by decide +kernel
theorem subd11_14_10 : subd11_14 [0, -4] = true := by decide +kernel
theorem subd11_14_11 : subd11_14 [0, -3] = true := by decide +kernel
theorem subd11_14_12 : subd11_14 [0, -2] = true := by decide +kernel
theorem subd11_14_13 : subd11_14 [0, -1] = true := by decide +kernel
theorem subd11_14_14 : subd11_14 [0, 0] = true := by decide +kernel
theorem subd11_14_15 : subd11_14 [0, 1] = true := by decide +kernel
theorem subd11_14_16 : subd11_14 [0, 2] = true := by decide +kernel
theorem subd11_14_17 : subd11_14 [0, 3] = true := by decide +kernel
theorem subd11_14_18 : subd11_14 [1, -4] = true := by decide +kernel
theorem subd11_14_19 : subd11_14 [1, -3] = true := by decide +kernel
theorem subd11_14_20 : subd11_14 [1, -2] = true := by decide +kernel
theorem subd11_14_21 : subd11_14 [1, -1] = true := by decide +kernel
theorem subd11_14_22 : subd11_14 [1, 0] = true := by decide +kernel
theorem subd11_14_23 : subd11_14 [1, 1] = true := by decide +kernel
theorem subd11_14_24 : subd11_14 [1, 2] = true := by decide +kernel
theorem subd11_14_25 : subd11_14 [1, 3] = true := by decide +kernel
theorem subd11_14_26 : subd11_14 [2] = true := by decide +kernel
theorem subd11_14_27 : subd11_14 [3] = true := by decide +kernel
theorem sbd11_14_0 : ∀ q ∈ blkd11_14_0, subd11_14 q = true := by
  unfold blkd11_14_0
  exact List.forall_mem_cons.2 ⟨subd11_14_0, List.forall_mem_cons.2 ⟨subd11_14_1, List.forall_mem_cons.2 ⟨subd11_14_2, List.forall_mem_cons.2 ⟨subd11_14_3, List.forall_mem_cons.2 ⟨subd11_14_4, List.forall_mem_cons.2 ⟨subd11_14_5, List.forall_mem_cons.2 ⟨subd11_14_6, List.forall_mem_cons.2 ⟨subd11_14_7, List.forall_mem_cons.2 ⟨subd11_14_8, List.forall_mem_cons.2 ⟨subd11_14_9, List.forall_mem_cons.2 ⟨subd11_14_10, List.forall_mem_cons.2 ⟨subd11_14_11, List.forall_mem_cons.2 ⟨subd11_14_12, List.forall_mem_cons.2 ⟨subd11_14_13, List.forall_mem_cons.2 ⟨subd11_14_14, List.forall_mem_cons.2 ⟨subd11_14_15, List.forall_mem_cons.2 ⟨subd11_14_16, List.forall_mem_cons.2 ⟨subd11_14_17, List.forall_mem_cons.2 ⟨subd11_14_18, List.forall_mem_cons.2 ⟨subd11_14_19, List.forall_mem_cons.2 ⟨subd11_14_20, List.forall_mem_cons.2 ⟨subd11_14_21, List.forall_mem_cons.2 ⟨subd11_14_22, List.forall_mem_cons.2 ⟨subd11_14_23, List.forall_mem_cons.2 ⟨subd11_14_24, List.forall_mem_cons.2 ⟨subd11_14_25, List.forall_mem_cons.2 ⟨subd11_14_26, List.forall_mem_cons.2 ⟨subd11_14_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_nil _⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_nil _⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_nil _⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_nil _⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_nil _⟩
theorem ld_okd12_5 : ldCheck G d12_5.U d12_5.ms ldd12_5 = true := by decide +kernel
theorem pre_okd12_5 : subPre G cell12 d12_5 = true := by decide +kernel
theorem subd12_5_0 : subd12_5 [] = true := by decide +kernel
theorem sbd12_5_0 : ∀ q ∈ blkd12_5_0, subd12_5 q = true := by
  unfold blkd12_5_0
  exact List.forall_mem_cons.2 ⟨subd12_5_0, List.forall_mem_nil _⟩
theorem ld_okd12_6 : ldCheck G d12_6.U d12_6.ms ldd12_6 = true := by decide +kernel
theorem pre_okd12_6 : subPre G cell12 d12_6 = true := by decide +kernel
theorem subd12_6_0 : subd12_6 [-2] = true := by decide +kernel
theorem subd12_6_1 : subd12_6 [-1] = true := by decide +kernel
theorem subd12_6_2 : subd12_6 [0] = true := by decide +kernel
theorem subd12_6_3 : subd12_6 [1] = true := by decide +kernel
theorem subd12_6_4 : subd12_6 [2] = true := by decide +kernel
theorem sbd12_6_0 : ∀ q ∈ blkd12_6_0, subd12_6 q = true := by
  unfold blkd12_6_0
  exact List.forall_mem_cons.2 ⟨subd12_6_0, List.forall_mem_cons.2 ⟨subd12_6_1, List.forall_mem_cons.2 ⟨subd12_6_2, List.forall_mem_cons.2 ⟨subd12_6_3, List.forall_mem_cons.2 ⟨subd12_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_7 : ldCheck G d12_7.U d12_7.ms ldd12_7 = true := by decide +kernel
theorem pre_okd12_7 : subPre G cell12 d12_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
