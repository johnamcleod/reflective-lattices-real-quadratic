import ReflectZphi.Data.Cert5.C117.Base

namespace ReflectZphi.Data.Cert5.C117

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_3_0 : subd5_3 [-2] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [2] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [0, 0, -7] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [0, 0, -6] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [0, 0, -5] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [0, 0, -4] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [0, 0, -3] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [0, 0, -2] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [0, 0, -1] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [0, 0, 0] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [0, 0, 1] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, 0, 2] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [0, 0, 3] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, 0, 4] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, 0, 5] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, 0, 6] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_nil _⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2, -4] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-2, -3] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-2, -1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-2, 0] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-2, 1] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-2, 2] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-1, -5] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-1, -4] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [1, 2] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_32 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [1, 4] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [2, -2] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [2, -1] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [2, 0] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [2, 1] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [2, 3] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C117
