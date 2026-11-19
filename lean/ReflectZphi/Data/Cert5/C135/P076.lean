import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_6_0 : subd11_6 [-3] = true := by decide +kernel
theorem subd11_6_1 : subd11_6 [-2, -3] = true := by decide +kernel
theorem subd11_6_2 : subd11_6 [-2, -2] = true := by decide +kernel
theorem subd11_6_3 : subd11_6 [-2, -1] = true := by decide +kernel
theorem subd11_6_4 : subd11_6 [-2, 0] = true := by decide +kernel
theorem subd11_6_5 : subd11_6 [-2, 1] = true := by decide +kernel
theorem subd11_6_6 : subd11_6 [-2, 2] = true := by decide +kernel
theorem subd11_6_7 : subd11_6 [-1, -4] = true := by decide +kernel
theorem subd11_6_8 : subd11_6 [-1, -3] = true := by decide +kernel
theorem subd11_6_9 : subd11_6 [-1, -2] = true := by decide +kernel
theorem subd11_6_10 : subd11_6 [-1, -1] = true := by decide +kernel
theorem subd11_6_11 : subd11_6 [-1, 0] = true := by decide +kernel
theorem subd11_6_12 : subd11_6 [-1, 1] = true := by decide +kernel
theorem subd11_6_13 : subd11_6 [-1, 2] = true := by decide +kernel
theorem subd11_6_14 : subd11_6 [-1, 3] = true := by decide +kernel
theorem subd11_6_15 : subd11_6 [0, -4] = true := by decide +kernel
theorem subd11_6_16 : subd11_6 [0, -3] = true := by decide +kernel
theorem subd11_6_17 : subd11_6 [0, -2] = true := by decide +kernel
theorem subd11_6_18 : subd11_6 [0, -1] = true := by decide +kernel
theorem subd11_6_19 : subd11_6 [0, 0] = true := by decide +kernel
theorem subd11_6_20 : subd11_6 [0, 1] = true := by decide +kernel
theorem subd11_6_21 : subd11_6 [0, 2] = true := by decide +kernel
theorem subd11_6_22 : subd11_6 [0, 3] = true := by decide +kernel
theorem subd11_6_23 : subd11_6 [1, -4] = true := by decide +kernel
theorem subd11_6_24 : subd11_6 [1, -3] = true := by decide +kernel
theorem subd11_6_25 : subd11_6 [1, -2] = true := by decide +kernel
theorem subd11_6_26 : subd11_6 [1, -1] = true := by decide +kernel
theorem subd11_6_27 : subd11_6 [1, 0] = true := by decide +kernel
theorem subd11_6_28 : subd11_6 [1, 1] = true := by decide +kernel
theorem subd11_6_29 : subd11_6 [1, 2] = true := by decide +kernel
theorem subd11_6_30 : subd11_6 [1, 3] = true := by decide +kernel
theorem subd11_6_31 : subd11_6 [2, -3] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_cons.2 ⟨subd11_6_1, List.forall_mem_cons.2 ⟨subd11_6_2, List.forall_mem_cons.2 ⟨subd11_6_3, List.forall_mem_cons.2 ⟨subd11_6_4, List.forall_mem_cons.2 ⟨subd11_6_5, List.forall_mem_cons.2 ⟨subd11_6_6, List.forall_mem_cons.2 ⟨subd11_6_7, List.forall_mem_cons.2 ⟨subd11_6_8, List.forall_mem_cons.2 ⟨subd11_6_9, List.forall_mem_cons.2 ⟨subd11_6_10, List.forall_mem_cons.2 ⟨subd11_6_11, List.forall_mem_cons.2 ⟨subd11_6_12, List.forall_mem_cons.2 ⟨subd11_6_13, List.forall_mem_cons.2 ⟨subd11_6_14, List.forall_mem_cons.2 ⟨subd11_6_15, List.forall_mem_cons.2 ⟨subd11_6_16, List.forall_mem_cons.2 ⟨subd11_6_17, List.forall_mem_cons.2 ⟨subd11_6_18, List.forall_mem_cons.2 ⟨subd11_6_19, List.forall_mem_cons.2 ⟨subd11_6_20, List.forall_mem_cons.2 ⟨subd11_6_21, List.forall_mem_cons.2 ⟨subd11_6_22, List.forall_mem_cons.2 ⟨subd11_6_23, List.forall_mem_cons.2 ⟨subd11_6_24, List.forall_mem_cons.2 ⟨subd11_6_25, List.forall_mem_cons.2 ⟨subd11_6_26, List.forall_mem_cons.2 ⟨subd11_6_27, List.forall_mem_cons.2 ⟨subd11_6_28, List.forall_mem_cons.2 ⟨subd11_6_29, List.forall_mem_cons.2 ⟨subd11_6_30, List.forall_mem_cons.2 ⟨subd11_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_6_32 : subd11_6 [2, -2] = true := by decide +kernel
theorem subd11_6_33 : subd11_6 [2, -1] = true := by decide +kernel
theorem subd11_6_34 : subd11_6 [2, 0] = true := by decide +kernel
theorem subd11_6_35 : subd11_6 [2, 1] = true := by decide +kernel
theorem subd11_6_36 : subd11_6 [2, 2] = true := by decide +kernel
theorem subd11_6_37 : subd11_6 [3] = true := by decide +kernel
theorem sbd11_6_1 : ∀ q ∈ blkd11_6_1, subd11_6 q = true := by
  unfold blkd11_6_1
  exact List.forall_mem_cons.2 ⟨subd11_6_32, List.forall_mem_cons.2 ⟨subd11_6_33, List.forall_mem_cons.2 ⟨subd11_6_34, List.forall_mem_cons.2 ⟨subd11_6_35, List.forall_mem_cons.2 ⟨subd11_6_36, List.forall_mem_cons.2 ⟨subd11_6_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd11_7 : ldCheck G d11_7.U d11_7.ms ldd11_7 = true := by decide +kernel
theorem pre_okd11_7 : subPre G cell11 d11_7 = true := by decide +kernel
theorem subd11_7_0 : subd11_7 [-3] = true := by decide +kernel
theorem subd11_7_1 : subd11_7 [-2, -3] = true := by decide +kernel
theorem subd11_7_2 : subd11_7 [-2, -2] = true := by decide +kernel
theorem subd11_7_3 : subd11_7 [-2, -1] = true := by decide +kernel
theorem subd11_7_4 : subd11_7 [-2, 0] = true := by decide +kernel
theorem subd11_7_5 : subd11_7 [-2, 1] = true := by decide +kernel
theorem subd11_7_6 : subd11_7 [-2, 2] = true := by decide +kernel
theorem subd11_7_7 : subd11_7 [-2, 3] = true := by decide +kernel
theorem subd11_7_8 : subd11_7 [-1, -4] = true := by decide +kernel
theorem subd11_7_9 : subd11_7 [-1, -3] = true := by decide +kernel
theorem subd11_7_10 : subd11_7 [-1, -2] = true := by decide +kernel
theorem subd11_7_11 : subd11_7 [-1, -1] = true := by decide +kernel
theorem subd11_7_12 : subd11_7 [-1, 0] = true := by decide +kernel
theorem subd11_7_13 : subd11_7 [-1, 1] = true := by decide +kernel
theorem subd11_7_14 : subd11_7 [-1, 2] = true := by decide +kernel
theorem subd11_7_15 : subd11_7 [-1, 3] = true := by decide +kernel
theorem subd11_7_16 : subd11_7 [0, -4] = true := by decide +kernel
theorem subd11_7_17 : subd11_7 [0, -3] = true := by decide +kernel
theorem subd11_7_18 : subd11_7 [0, -2] = true := by decide +kernel
theorem subd11_7_19 : subd11_7 [0, -1] = true := by decide +kernel
theorem subd11_7_20 : subd11_7 [0, 0] = true := by decide +kernel
theorem subd11_7_21 : subd11_7 [0, 1] = true := by decide +kernel
theorem subd11_7_22 : subd11_7 [0, 2] = true := by decide +kernel
theorem subd11_7_23 : subd11_7 [0, 3] = true := by decide +kernel
theorem subd11_7_24 : subd11_7 [1, -4] = true := by decide +kernel
theorem subd11_7_25 : subd11_7 [1, -3] = true := by decide +kernel
theorem subd11_7_26 : subd11_7 [1, -2] = true := by decide +kernel
theorem subd11_7_27 : subd11_7 [1, -1] = true := by decide +kernel
theorem subd11_7_28 : subd11_7 [1, 0] = true := by decide +kernel
theorem subd11_7_29 : subd11_7 [1, 1] = true := by decide +kernel
theorem subd11_7_30 : subd11_7 [1, 2] = true := by decide +kernel
theorem subd11_7_31 : subd11_7 [1, 3] = true := by decide +kernel
theorem sbd11_7_0 : ∀ q ∈ blkd11_7_0, subd11_7 q = true := by
  unfold blkd11_7_0
  exact List.forall_mem_cons.2 ⟨subd11_7_0, List.forall_mem_cons.2 ⟨subd11_7_1, List.forall_mem_cons.2 ⟨subd11_7_2, List.forall_mem_cons.2 ⟨subd11_7_3, List.forall_mem_cons.2 ⟨subd11_7_4, List.forall_mem_cons.2 ⟨subd11_7_5, List.forall_mem_cons.2 ⟨subd11_7_6, List.forall_mem_cons.2 ⟨subd11_7_7, List.forall_mem_cons.2 ⟨subd11_7_8, List.forall_mem_cons.2 ⟨subd11_7_9, List.forall_mem_cons.2 ⟨subd11_7_10, List.forall_mem_cons.2 ⟨subd11_7_11, List.forall_mem_cons.2 ⟨subd11_7_12, List.forall_mem_cons.2 ⟨subd11_7_13, List.forall_mem_cons.2 ⟨subd11_7_14, List.forall_mem_cons.2 ⟨subd11_7_15, List.forall_mem_cons.2 ⟨subd11_7_16, List.forall_mem_cons.2 ⟨subd11_7_17, List.forall_mem_cons.2 ⟨subd11_7_18, List.forall_mem_cons.2 ⟨subd11_7_19, List.forall_mem_cons.2 ⟨subd11_7_20, List.forall_mem_cons.2 ⟨subd11_7_21, List.forall_mem_cons.2 ⟨subd11_7_22, List.forall_mem_cons.2 ⟨subd11_7_23, List.forall_mem_cons.2 ⟨subd11_7_24, List.forall_mem_cons.2 ⟨subd11_7_25, List.forall_mem_cons.2 ⟨subd11_7_26, List.forall_mem_cons.2 ⟨subd11_7_27, List.forall_mem_cons.2 ⟨subd11_7_28, List.forall_mem_cons.2 ⟨subd11_7_29, List.forall_mem_cons.2 ⟨subd11_7_30, List.forall_mem_cons.2 ⟨subd11_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_7_32 : subd11_7 [2, -4] = true := by decide +kernel
theorem subd11_7_33 : subd11_7 [2, -3] = true := by decide +kernel
theorem subd11_7_34 : subd11_7 [2, -2] = true := by decide +kernel
theorem subd11_7_35 : subd11_7 [2, -1] = true := by decide +kernel
theorem subd11_7_36 : subd11_7 [2, 0] = true := by decide +kernel
theorem subd11_7_37 : subd11_7 [2, 1] = true := by decide +kernel
theorem subd11_7_38 : subd11_7 [2, 2] = true := by decide +kernel
theorem subd11_7_39 : subd11_7 [3] = true := by decide +kernel
theorem sbd11_7_1 : ∀ q ∈ blkd11_7_1, subd11_7 q = true := by
  unfold blkd11_7_1
  exact List.forall_mem_cons.2 ⟨subd11_7_32, List.forall_mem_cons.2 ⟨subd11_7_33, List.forall_mem_cons.2 ⟨subd11_7_34, List.forall_mem_cons.2 ⟨subd11_7_35, List.forall_mem_cons.2 ⟨subd11_7_36, List.forall_mem_cons.2 ⟨subd11_7_37, List.forall_mem_cons.2 ⟨subd11_7_38, List.forall_mem_cons.2 ⟨subd11_7_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-2] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-1, -1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-1, 0] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-1, 1] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-1, 2] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [0, -2] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [1, -2] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [1, -1] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [1, 0] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [1, 1] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [2] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
