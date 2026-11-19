import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-1, -4] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-1, -3] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-1, -2] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-1, -1] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-1, 0] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-1, 1] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [2] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [3] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-3] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-2, -3] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-2, 2] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-2, 3] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [-1, 4] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [1, -5] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [1, 1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [2, -4] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [2, -3] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [2, -2] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [2, -1] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [2, 0] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [2, 1] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [2, 2] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [3] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [2] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C130
