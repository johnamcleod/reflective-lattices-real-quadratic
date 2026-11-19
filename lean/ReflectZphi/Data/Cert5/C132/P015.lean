import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-3] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [1] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [2] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [3] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [1] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [2] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [2, 0] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [2, 2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C132
