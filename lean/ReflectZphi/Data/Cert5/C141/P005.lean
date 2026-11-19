import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-3] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-1, 4] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [1, 1] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [3] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-5] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-4, -5] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-4, -4] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-4, -3] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-4, -2] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-4, -1] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-4, 0] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-4, 1] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-3, -5] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-3, -4] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-3, -3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-3, -2] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [-3, -1] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [-3, 0] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [-3, 1] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [-3, 2] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [-2, -5] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [-2, -4] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [-2, -3] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [-2, -2] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [-2, -1] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [-2, 0] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [-2, 1] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [-2, 2] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [-2, 3] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [-1, -5] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [-1, 1] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
