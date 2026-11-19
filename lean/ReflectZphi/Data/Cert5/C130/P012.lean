import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-3] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-2, -4] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-1, -4] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-1, 3] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [0, -4] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [0, 3] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [1, -4] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [1, 3] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [2, 0] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [2, 2] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [2, 3] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [3] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-2] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-1] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [0, -2] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [1] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [2] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-3] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-1, -1] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-1, 0] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-1, 1] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-1, 2] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [0, -4] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [0, -1] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [0, 0] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [0, 1] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [0, 3] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [1, -3] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [1, -1] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [1, 0] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [2] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [3] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C130
