import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_8_0 : subd11_8 [-1, -2] = true := by decide +kernel
theorem subd11_8_1 : subd11_8 [-1, -1] = true := by decide +kernel
theorem subd11_8_2 : subd11_8 [-1, 0] = true := by decide +kernel
theorem subd11_8_3 : subd11_8 [-1, 1] = true := by decide +kernel
theorem subd11_8_4 : subd11_8 [0, -2] = true := by decide +kernel
theorem subd11_8_5 : subd11_8 [0, -1] = true := by decide +kernel
theorem subd11_8_6 : subd11_8 [0, 0, -8] = true := by decide +kernel
theorem subd11_8_7 : subd11_8 [0, 0, -7] = true := by decide +kernel
theorem subd11_8_8 : subd11_8 [0, 0, -6] = true := by decide +kernel
theorem subd11_8_9 : subd11_8 [0, 0, -5] = true := by decide +kernel
theorem subd11_8_10 : subd11_8 [0, 0, -4] = true := by decide +kernel
theorem subd11_8_11 : subd11_8 [0, 0, -3] = true := by decide +kernel
theorem subd11_8_12 : subd11_8 [0, 0, -2] = true := by decide +kernel
theorem subd11_8_13 : subd11_8 [0, 0, -1] = true := by decide +kernel
theorem subd11_8_14 : subd11_8 [0, 0, 0] = true := by decide +kernel
theorem subd11_8_15 : subd11_8 [0, 0, 1] = true := by decide +kernel
theorem subd11_8_16 : subd11_8 [0, 0, 2] = true := by decide +kernel
theorem subd11_8_17 : subd11_8 [0, 0, 3] = true := by decide +kernel
theorem subd11_8_18 : subd11_8 [0, 0, 4] = true := by decide +kernel
theorem subd11_8_19 : subd11_8 [0, 0, 5] = true := by decide +kernel
theorem subd11_8_20 : subd11_8 [0, 0, 6] = true := by decide +kernel
theorem subd11_8_21 : subd11_8 [0, 0, 7] = true := by decide +kernel
theorem subd11_8_22 : subd11_8 [0, 1] = true := by decide +kernel
theorem subd11_8_23 : subd11_8 [1, -2] = true := by decide +kernel
theorem subd11_8_24 : subd11_8 [1, -1] = true := by decide +kernel
theorem subd11_8_25 : subd11_8 [1, 0] = true := by decide +kernel
theorem subd11_8_26 : subd11_8 [1, 1] = true := by decide +kernel
theorem sbd11_8_0 : ∀ q ∈ blkd11_8_0, subd11_8 q = true := by
  unfold blkd11_8_0
  exact List.forall_mem_cons.2 ⟨subd11_8_0, List.forall_mem_cons.2 ⟨subd11_8_1, List.forall_mem_cons.2 ⟨subd11_8_2, List.forall_mem_cons.2 ⟨subd11_8_3, List.forall_mem_cons.2 ⟨subd11_8_4, List.forall_mem_cons.2 ⟨subd11_8_5, List.forall_mem_cons.2 ⟨subd11_8_6, List.forall_mem_cons.2 ⟨subd11_8_7, List.forall_mem_cons.2 ⟨subd11_8_8, List.forall_mem_cons.2 ⟨subd11_8_9, List.forall_mem_cons.2 ⟨subd11_8_10, List.forall_mem_cons.2 ⟨subd11_8_11, List.forall_mem_cons.2 ⟨subd11_8_12, List.forall_mem_cons.2 ⟨subd11_8_13, List.forall_mem_cons.2 ⟨subd11_8_14, List.forall_mem_cons.2 ⟨subd11_8_15, List.forall_mem_cons.2 ⟨subd11_8_16, List.forall_mem_cons.2 ⟨subd11_8_17, List.forall_mem_cons.2 ⟨subd11_8_18, List.forall_mem_cons.2 ⟨subd11_8_19, List.forall_mem_cons.2 ⟨subd11_8_20, List.forall_mem_cons.2 ⟨subd11_8_21, List.forall_mem_cons.2 ⟨subd11_8_22, List.forall_mem_cons.2 ⟨subd11_8_23, List.forall_mem_cons.2 ⟨subd11_8_24, List.forall_mem_cons.2 ⟨subd11_8_25, List.forall_mem_cons.2 ⟨subd11_8_26, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_9 : ldCheck G d11_9.U d11_9.ms ldd11_9 = true := by decide +kernel
theorem pre_okd11_9 : subPre G cell11 d11_9 = true := by decide +kernel
theorem subd11_9_0 : subd11_9 [-2] = true := by decide +kernel
theorem subd11_9_1 : subd11_9 [-1, -3] = true := by decide +kernel
theorem subd11_9_2 : subd11_9 [-1, -2] = true := by decide +kernel
theorem subd11_9_3 : subd11_9 [-1, -1] = true := by decide +kernel
theorem subd11_9_4 : subd11_9 [-1, 0] = true := by decide +kernel
theorem subd11_9_5 : subd11_9 [-1, 1] = true := by decide +kernel
theorem subd11_9_6 : subd11_9 [-1, 2] = true := by decide +kernel
theorem subd11_9_7 : subd11_9 [0, -3] = true := by decide +kernel
theorem subd11_9_8 : subd11_9 [0, -2] = true := by decide +kernel
theorem subd11_9_9 : subd11_9 [0, -1] = true := by decide +kernel
theorem subd11_9_10 : subd11_9 [0, 0] = true := by decide +kernel
theorem subd11_9_11 : subd11_9 [0, 1] = true := by decide +kernel
theorem subd11_9_12 : subd11_9 [0, 2] = true := by decide +kernel
theorem subd11_9_13 : subd11_9 [1, -3] = true := by decide +kernel
theorem subd11_9_14 : subd11_9 [1, -2] = true := by decide +kernel
theorem subd11_9_15 : subd11_9 [1, -1] = true := by decide +kernel
theorem subd11_9_16 : subd11_9 [1, 0] = true := by decide +kernel
theorem subd11_9_17 : subd11_9 [1, 1] = true := by decide +kernel
theorem subd11_9_18 : subd11_9 [1, 2] = true := by decide +kernel
theorem subd11_9_19 : subd11_9 [2] = true := by decide +kernel
theorem sbd11_9_0 : ∀ q ∈ blkd11_9_0, subd11_9 q = true := by
  unfold blkd11_9_0
  exact List.forall_mem_cons.2 ⟨subd11_9_0, List.forall_mem_cons.2 ⟨subd11_9_1, List.forall_mem_cons.2 ⟨subd11_9_2, List.forall_mem_cons.2 ⟨subd11_9_3, List.forall_mem_cons.2 ⟨subd11_9_4, List.forall_mem_cons.2 ⟨subd11_9_5, List.forall_mem_cons.2 ⟨subd11_9_6, List.forall_mem_cons.2 ⟨subd11_9_7, List.forall_mem_cons.2 ⟨subd11_9_8, List.forall_mem_cons.2 ⟨subd11_9_9, List.forall_mem_cons.2 ⟨subd11_9_10, List.forall_mem_cons.2 ⟨subd11_9_11, List.forall_mem_cons.2 ⟨subd11_9_12, List.forall_mem_cons.2 ⟨subd11_9_13, List.forall_mem_cons.2 ⟨subd11_9_14, List.forall_mem_cons.2 ⟨subd11_9_15, List.forall_mem_cons.2 ⟨subd11_9_16, List.forall_mem_cons.2 ⟨subd11_9_17, List.forall_mem_cons.2 ⟨subd11_9_18, List.forall_mem_cons.2 ⟨subd11_9_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem subd11_11_0 : subd11_11 [-2] = true := by decide +kernel
theorem subd11_11_1 : subd11_11 [-1] = true := by decide +kernel
theorem subd11_11_2 : subd11_11 [0, -3] = true := by decide +kernel
theorem subd11_11_3 : subd11_11 [0, -2] = true := by decide +kernel
theorem subd11_11_4 : subd11_11 [0, -1] = true := by decide +kernel
theorem subd11_11_5 : subd11_11 [0, 0] = true := by decide +kernel
theorem subd11_11_6 : subd11_11 [0, 1] = true := by decide +kernel
theorem subd11_11_7 : subd11_11 [0, 2] = true := by decide +kernel
theorem subd11_11_8 : subd11_11 [1] = true := by decide +kernel
theorem subd11_11_9 : subd11_11 [2] = true := by decide +kernel
theorem sbd11_11_0 : ∀ q ∈ blkd11_11_0, subd11_11 q = true := by
  unfold blkd11_11_0
  exact List.forall_mem_cons.2 ⟨subd11_11_0, List.forall_mem_cons.2 ⟨subd11_11_1, List.forall_mem_cons.2 ⟨subd11_11_2, List.forall_mem_cons.2 ⟨subd11_11_3, List.forall_mem_cons.2 ⟨subd11_11_4, List.forall_mem_cons.2 ⟨subd11_11_5, List.forall_mem_cons.2 ⟨subd11_11_6, List.forall_mem_cons.2 ⟨subd11_11_7, List.forall_mem_cons.2 ⟨subd11_11_8, List.forall_mem_cons.2 ⟨subd11_11_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_12 : ldCheck G d11_12.U d11_12.ms ldd11_12 = true := by decide +kernel
theorem pre_okd11_12 : subPre G cell11 d11_12 = true := by decide +kernel
theorem subd11_12_0 : subd11_12 [-1] = true := by decide +kernel
theorem subd11_12_1 : subd11_12 [0] = true := by decide +kernel
theorem subd11_12_2 : subd11_12 [1] = true := by decide +kernel
theorem sbd11_12_0 : ∀ q ∈ blkd11_12_0, subd11_12 q = true := by
  unfold blkd11_12_0
  exact List.forall_mem_cons.2 ⟨subd11_12_0, List.forall_mem_cons.2 ⟨subd11_12_1, List.forall_mem_cons.2 ⟨subd11_12_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd11_13 : ldCheck G d11_13.U d11_13.ms ldd11_13 = true := by decide +kernel
theorem pre_okd11_13 : subPre G cell11 d11_13 = true := by decide +kernel
theorem subd11_13_0 : subd11_13 [] = true := by decide +kernel
theorem sbd11_13_0 : ∀ q ∈ blkd11_13_0, subd11_13 q = true := by
  unfold blkd11_13_0
  exact List.forall_mem_cons.2 ⟨subd11_13_0, List.forall_mem_nil _⟩
theorem ld_okd11_14 : ldCheck G d11_14.U d11_14.ms ldd11_14 = true := by decide +kernel
theorem pre_okd11_14 : subPre G cell11 d11_14 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
