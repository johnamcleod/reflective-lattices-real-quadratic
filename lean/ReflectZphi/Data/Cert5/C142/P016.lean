import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1, -4] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [1, 3] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-3] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-2, -4] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-2, -1] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-2, 0] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-2, 1] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [2, 0] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [2, 3] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [3] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [2] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
