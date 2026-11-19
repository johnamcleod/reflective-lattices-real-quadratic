import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel
theorem subd18_2_0 : subd18_2 [] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_nil _⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_nil _⟩
theorem ld_okd18_4 : ldCheck G d18_4.U d18_4.ms ldd18_4 = true := by decide +kernel
theorem pre_okd18_4 : subPre G cell18 d18_4 = true := by decide +kernel
theorem subd18_4_0 : subd18_4 [-3] = true := by decide +kernel
theorem subd18_4_1 : subd18_4 [-2, -2] = true := by decide +kernel
theorem subd18_4_2 : subd18_4 [-2, -1] = true := by decide +kernel
theorem subd18_4_3 : subd18_4 [-2, 0] = true := by decide +kernel
theorem subd18_4_4 : subd18_4 [-2, 1] = true := by decide +kernel
theorem subd18_4_5 : subd18_4 [-2, 2] = true := by decide +kernel
theorem subd18_4_6 : subd18_4 [-2, 3] = true := by decide +kernel
theorem subd18_4_7 : subd18_4 [-1, -3] = true := by decide +kernel
theorem subd18_4_8 : subd18_4 [-1, -2] = true := by decide +kernel
theorem subd18_4_9 : subd18_4 [-1, -1] = true := by decide +kernel
theorem subd18_4_10 : subd18_4 [-1, 0] = true := by decide +kernel
theorem subd18_4_11 : subd18_4 [-1, 1] = true := by decide +kernel
theorem subd18_4_12 : subd18_4 [-1, 2] = true := by decide +kernel
theorem subd18_4_13 : subd18_4 [-1, 3] = true := by decide +kernel
theorem subd18_4_14 : subd18_4 [0, -4] = true := by decide +kernel
theorem subd18_4_15 : subd18_4 [0, -3] = true := by decide +kernel
theorem subd18_4_16 : subd18_4 [0, -2] = true := by decide +kernel
theorem subd18_4_17 : subd18_4 [0, -1] = true := by decide +kernel
theorem subd18_4_18 : subd18_4 [0, 0] = true := by decide +kernel
theorem subd18_4_19 : subd18_4 [0, 1] = true := by decide +kernel
theorem subd18_4_20 : subd18_4 [0, 2] = true := by decide +kernel
theorem subd18_4_21 : subd18_4 [0, 3] = true := by decide +kernel
theorem subd18_4_22 : subd18_4 [1, -4] = true := by decide +kernel
theorem subd18_4_23 : subd18_4 [1, -3] = true := by decide +kernel
theorem subd18_4_24 : subd18_4 [1, -2] = true := by decide +kernel
theorem subd18_4_25 : subd18_4 [1, -1] = true := by decide +kernel
theorem subd18_4_26 : subd18_4 [1, 0] = true := by decide +kernel
theorem subd18_4_27 : subd18_4 [1, 1] = true := by decide +kernel
theorem subd18_4_28 : subd18_4 [1, 2] = true := by decide +kernel
theorem subd18_4_29 : subd18_4 [2, -4] = true := by decide +kernel
theorem subd18_4_30 : subd18_4 [2, -3] = true := by decide +kernel
theorem subd18_4_31 : subd18_4 [2, -2] = true := by decide +kernel
theorem sbd18_4_0 : ∀ q ∈ blkd18_4_0, subd18_4 q = true := by
  unfold blkd18_4_0
  exact List.forall_mem_cons.2 ⟨subd18_4_0, List.forall_mem_cons.2 ⟨subd18_4_1, List.forall_mem_cons.2 ⟨subd18_4_2, List.forall_mem_cons.2 ⟨subd18_4_3, List.forall_mem_cons.2 ⟨subd18_4_4, List.forall_mem_cons.2 ⟨subd18_4_5, List.forall_mem_cons.2 ⟨subd18_4_6, List.forall_mem_cons.2 ⟨subd18_4_7, List.forall_mem_cons.2 ⟨subd18_4_8, List.forall_mem_cons.2 ⟨subd18_4_9, List.forall_mem_cons.2 ⟨subd18_4_10, List.forall_mem_cons.2 ⟨subd18_4_11, List.forall_mem_cons.2 ⟨subd18_4_12, List.forall_mem_cons.2 ⟨subd18_4_13, List.forall_mem_cons.2 ⟨subd18_4_14, List.forall_mem_cons.2 ⟨subd18_4_15, List.forall_mem_cons.2 ⟨subd18_4_16, List.forall_mem_cons.2 ⟨subd18_4_17, List.forall_mem_cons.2 ⟨subd18_4_18, List.forall_mem_cons.2 ⟨subd18_4_19, List.forall_mem_cons.2 ⟨subd18_4_20, List.forall_mem_cons.2 ⟨subd18_4_21, List.forall_mem_cons.2 ⟨subd18_4_22, List.forall_mem_cons.2 ⟨subd18_4_23, List.forall_mem_cons.2 ⟨subd18_4_24, List.forall_mem_cons.2 ⟨subd18_4_25, List.forall_mem_cons.2 ⟨subd18_4_26, List.forall_mem_cons.2 ⟨subd18_4_27, List.forall_mem_cons.2 ⟨subd18_4_28, List.forall_mem_cons.2 ⟨subd18_4_29, List.forall_mem_cons.2 ⟨subd18_4_30, List.forall_mem_cons.2 ⟨subd18_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_4_32 : subd18_4 [2, -1] = true := by decide +kernel
theorem subd18_4_33 : subd18_4 [2, 0] = true := by decide +kernel
theorem subd18_4_34 : subd18_4 [2, 1] = true := by decide +kernel
theorem subd18_4_35 : subd18_4 [3] = true := by decide +kernel
theorem sbd18_4_1 : ∀ q ∈ blkd18_4_1, subd18_4 q = true := by
  unfold blkd18_4_1
  exact List.forall_mem_cons.2 ⟨subd18_4_32, List.forall_mem_cons.2 ⟨subd18_4_33, List.forall_mem_cons.2 ⟨subd18_4_34, List.forall_mem_cons.2 ⟨subd18_4_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd18_5 : ldCheck G d18_5.U d18_5.ms ldd18_5 = true := by decide +kernel
theorem pre_okd18_5 : subPre G cell18 d18_5 = true := by decide +kernel
theorem subd18_5_0 : subd18_5 [-2] = true := by decide +kernel
theorem subd18_5_1 : subd18_5 [-1] = true := by decide +kernel
theorem subd18_5_2 : subd18_5 [0] = true := by decide +kernel
theorem subd18_5_3 : subd18_5 [1] = true := by decide +kernel
theorem subd18_5_4 : subd18_5 [2] = true := by decide +kernel
theorem sbd18_5_0 : ∀ q ∈ blkd18_5_0, subd18_5 q = true := by
  unfold blkd18_5_0
  exact List.forall_mem_cons.2 ⟨subd18_5_0, List.forall_mem_cons.2 ⟨subd18_5_1, List.forall_mem_cons.2 ⟨subd18_5_2, List.forall_mem_cons.2 ⟨subd18_5_3, List.forall_mem_cons.2 ⟨subd18_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd18_6 : ldCheck G d18_6.U d18_6.ms ldd18_6 = true := by decide +kernel
theorem pre_okd18_6 : subPre G cell18 d18_6 = true := by decide +kernel
theorem subd18_6_0 : subd18_6 [-3] = true := by decide +kernel
theorem subd18_6_1 : subd18_6 [-2] = true := by decide +kernel
theorem subd18_6_2 : subd18_6 [-1, -4] = true := by decide +kernel
theorem subd18_6_3 : subd18_6 [-1, -3] = true := by decide +kernel
theorem subd18_6_4 : subd18_6 [-1, -2] = true := by decide +kernel
theorem subd18_6_5 : subd18_6 [-1, -1] = true := by decide +kernel
theorem subd18_6_6 : subd18_6 [-1, 0] = true := by decide +kernel
theorem subd18_6_7 : subd18_6 [-1, 1] = true := by decide +kernel
theorem subd18_6_8 : subd18_6 [-1, 2] = true := by decide +kernel
theorem subd18_6_9 : subd18_6 [-1, 3] = true := by decide +kernel
theorem subd18_6_10 : subd18_6 [0, -4] = true := by decide +kernel
theorem subd18_6_11 : subd18_6 [0, -3] = true := by decide +kernel
theorem subd18_6_12 : subd18_6 [0, -2] = true := by decide +kernel
theorem subd18_6_13 : subd18_6 [0, -1] = true := by decide +kernel
theorem subd18_6_14 : subd18_6 [0, 0] = true := by decide +kernel
theorem subd18_6_15 : subd18_6 [0, 1] = true := by decide +kernel
theorem subd18_6_16 : subd18_6 [0, 2] = true := by decide +kernel
theorem subd18_6_17 : subd18_6 [0, 3] = true := by decide +kernel
theorem subd18_6_18 : subd18_6 [1, -4] = true := by decide +kernel
theorem subd18_6_19 : subd18_6 [1, -3] = true := by decide +kernel
theorem subd18_6_20 : subd18_6 [1, -2] = true := by decide +kernel
theorem subd18_6_21 : subd18_6 [1, -1] = true := by decide +kernel
theorem subd18_6_22 : subd18_6 [1, 0] = true := by decide +kernel
theorem subd18_6_23 : subd18_6 [1, 1] = true := by decide +kernel
theorem subd18_6_24 : subd18_6 [1, 2] = true := by decide +kernel
theorem subd18_6_25 : subd18_6 [1, 3] = true := by decide +kernel
theorem subd18_6_26 : subd18_6 [2] = true := by decide +kernel
theorem subd18_6_27 : subd18_6 [3] = true := by decide +kernel
theorem sbd18_6_0 : ∀ q ∈ blkd18_6_0, subd18_6 q = true := by
  unfold blkd18_6_0
  exact List.forall_mem_cons.2 ⟨subd18_6_0, List.forall_mem_cons.2 ⟨subd18_6_1, List.forall_mem_cons.2 ⟨subd18_6_2, List.forall_mem_cons.2 ⟨subd18_6_3, List.forall_mem_cons.2 ⟨subd18_6_4, List.forall_mem_cons.2 ⟨subd18_6_5, List.forall_mem_cons.2 ⟨subd18_6_6, List.forall_mem_cons.2 ⟨subd18_6_7, List.forall_mem_cons.2 ⟨subd18_6_8, List.forall_mem_cons.2 ⟨subd18_6_9, List.forall_mem_cons.2 ⟨subd18_6_10, List.forall_mem_cons.2 ⟨subd18_6_11, List.forall_mem_cons.2 ⟨subd18_6_12, List.forall_mem_cons.2 ⟨subd18_6_13, List.forall_mem_cons.2 ⟨subd18_6_14, List.forall_mem_cons.2 ⟨subd18_6_15, List.forall_mem_cons.2 ⟨subd18_6_16, List.forall_mem_cons.2 ⟨subd18_6_17, List.forall_mem_cons.2 ⟨subd18_6_18, List.forall_mem_cons.2 ⟨subd18_6_19, List.forall_mem_cons.2 ⟨subd18_6_20, List.forall_mem_cons.2 ⟨subd18_6_21, List.forall_mem_cons.2 ⟨subd18_6_22, List.forall_mem_cons.2 ⟨subd18_6_23, List.forall_mem_cons.2 ⟨subd18_6_24, List.forall_mem_cons.2 ⟨subd18_6_25, List.forall_mem_cons.2 ⟨subd18_6_26, List.forall_mem_cons.2 ⟨subd18_6_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_7 : ldCheck G d18_7.U d18_7.ms ldd18_7 = true := by decide +kernel
theorem pre_okd18_7 : subPre G cell18 d18_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
