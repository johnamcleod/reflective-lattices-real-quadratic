import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_0 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [2, 2] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-3] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [1, 3] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [2, -4] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [3] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
