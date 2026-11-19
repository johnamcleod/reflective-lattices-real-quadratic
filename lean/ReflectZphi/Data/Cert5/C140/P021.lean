import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_nil _⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel
theorem subd16_2_0 : subd16_2 [-1] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [0] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [1] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [-3] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [-2, -4] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [-2, -3] = true := by decide +kernel
theorem subd16_3_3 : subd16_3 [-2, -2] = true := by decide +kernel
theorem subd16_3_4 : subd16_3 [-2, -1] = true := by decide +kernel
theorem subd16_3_5 : subd16_3 [-2, 0] = true := by decide +kernel
theorem subd16_3_6 : subd16_3 [-2, 1] = true := by decide +kernel
theorem subd16_3_7 : subd16_3 [-2, 2] = true := by decide +kernel
theorem subd16_3_8 : subd16_3 [-1, -4] = true := by decide +kernel
theorem subd16_3_9 : subd16_3 [-1, -3] = true := by decide +kernel
theorem subd16_3_10 : subd16_3 [-1, -2] = true := by decide +kernel
theorem subd16_3_11 : subd16_3 [-1, -1] = true := by decide +kernel
theorem subd16_3_12 : subd16_3 [-1, 0] = true := by decide +kernel
theorem subd16_3_13 : subd16_3 [-1, 1] = true := by decide +kernel
theorem subd16_3_14 : subd16_3 [-1, 2] = true := by decide +kernel
theorem subd16_3_15 : subd16_3 [-1, 3] = true := by decide +kernel
theorem subd16_3_16 : subd16_3 [0, -4] = true := by decide +kernel
theorem subd16_3_17 : subd16_3 [0, -3] = true := by decide +kernel
theorem subd16_3_18 : subd16_3 [0, -2] = true := by decide +kernel
theorem subd16_3_19 : subd16_3 [0, -1] = true := by decide +kernel
theorem subd16_3_20 : subd16_3 [0, 0] = true := by decide +kernel
theorem subd16_3_21 : subd16_3 [0, 1] = true := by decide +kernel
theorem subd16_3_22 : subd16_3 [0, 2] = true := by decide +kernel
theorem subd16_3_23 : subd16_3 [0, 3] = true := by decide +kernel
theorem subd16_3_24 : subd16_3 [1, -4] = true := by decide +kernel
theorem subd16_3_25 : subd16_3 [1, -3] = true := by decide +kernel
theorem subd16_3_26 : subd16_3 [1, -2] = true := by decide +kernel
theorem subd16_3_27 : subd16_3 [1, -1] = true := by decide +kernel
theorem subd16_3_28 : subd16_3 [1, 0] = true := by decide +kernel
theorem subd16_3_29 : subd16_3 [1, 1] = true := by decide +kernel
theorem subd16_3_30 : subd16_3 [1, 2] = true := by decide +kernel
theorem subd16_3_31 : subd16_3 [1, 3] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_cons.2 ⟨subd16_3_3, List.forall_mem_cons.2 ⟨subd16_3_4, List.forall_mem_cons.2 ⟨subd16_3_5, List.forall_mem_cons.2 ⟨subd16_3_6, List.forall_mem_cons.2 ⟨subd16_3_7, List.forall_mem_cons.2 ⟨subd16_3_8, List.forall_mem_cons.2 ⟨subd16_3_9, List.forall_mem_cons.2 ⟨subd16_3_10, List.forall_mem_cons.2 ⟨subd16_3_11, List.forall_mem_cons.2 ⟨subd16_3_12, List.forall_mem_cons.2 ⟨subd16_3_13, List.forall_mem_cons.2 ⟨subd16_3_14, List.forall_mem_cons.2 ⟨subd16_3_15, List.forall_mem_cons.2 ⟨subd16_3_16, List.forall_mem_cons.2 ⟨subd16_3_17, List.forall_mem_cons.2 ⟨subd16_3_18, List.forall_mem_cons.2 ⟨subd16_3_19, List.forall_mem_cons.2 ⟨subd16_3_20, List.forall_mem_cons.2 ⟨subd16_3_21, List.forall_mem_cons.2 ⟨subd16_3_22, List.forall_mem_cons.2 ⟨subd16_3_23, List.forall_mem_cons.2 ⟨subd16_3_24, List.forall_mem_cons.2 ⟨subd16_3_25, List.forall_mem_cons.2 ⟨subd16_3_26, List.forall_mem_cons.2 ⟨subd16_3_27, List.forall_mem_cons.2 ⟨subd16_3_28, List.forall_mem_cons.2 ⟨subd16_3_29, List.forall_mem_cons.2 ⟨subd16_3_30, List.forall_mem_cons.2 ⟨subd16_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_3_32 : subd16_3 [2, -3] = true := by decide +kernel
theorem subd16_3_33 : subd16_3 [2, -2] = true := by decide +kernel
theorem subd16_3_34 : subd16_3 [2, -1] = true := by decide +kernel
theorem subd16_3_35 : subd16_3 [2, 0] = true := by decide +kernel
theorem subd16_3_36 : subd16_3 [2, 1] = true := by decide +kernel
theorem subd16_3_37 : subd16_3 [2, 2] = true := by decide +kernel
theorem subd16_3_38 : subd16_3 [2, 3] = true := by decide +kernel
theorem subd16_3_39 : subd16_3 [3] = true := by decide +kernel
theorem sbd16_3_1 : ∀ q ∈ blkd16_3_1, subd16_3 q = true := by
  unfold blkd16_3_1
  exact List.forall_mem_cons.2 ⟨subd16_3_32, List.forall_mem_cons.2 ⟨subd16_3_33, List.forall_mem_cons.2 ⟨subd16_3_34, List.forall_mem_cons.2 ⟨subd16_3_35, List.forall_mem_cons.2 ⟨subd16_3_36, List.forall_mem_cons.2 ⟨subd16_3_37, List.forall_mem_cons.2 ⟨subd16_3_38, List.forall_mem_cons.2 ⟨subd16_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_4 : ldCheck G d16_4.U d16_4.ms ldd16_4 = true := by decide +kernel
theorem pre_okd16_4 : subPre G cell16 d16_4 = true := by decide +kernel
theorem subd16_4_0 : subd16_4 [-2] = true := by decide +kernel
theorem subd16_4_1 : subd16_4 [-1, -3] = true := by decide +kernel
theorem subd16_4_2 : subd16_4 [-1, -2] = true := by decide +kernel
theorem subd16_4_3 : subd16_4 [-1, -1] = true := by decide +kernel
theorem subd16_4_4 : subd16_4 [-1, 0] = true := by decide +kernel
theorem subd16_4_5 : subd16_4 [-1, 1] = true := by decide +kernel
theorem subd16_4_6 : subd16_4 [-1, 2] = true := by decide +kernel
theorem subd16_4_7 : subd16_4 [0, -3] = true := by decide +kernel
theorem subd16_4_8 : subd16_4 [0, -2] = true := by decide +kernel
theorem subd16_4_9 : subd16_4 [0, -1] = true := by decide +kernel
theorem subd16_4_10 : subd16_4 [0, 0] = true := by decide +kernel
theorem subd16_4_11 : subd16_4 [0, 1] = true := by decide +kernel
theorem subd16_4_12 : subd16_4 [0, 2] = true := by decide +kernel
theorem subd16_4_13 : subd16_4 [1, -3] = true := by decide +kernel
theorem subd16_4_14 : subd16_4 [1, -2] = true := by decide +kernel
theorem subd16_4_15 : subd16_4 [1, -1] = true := by decide +kernel
theorem subd16_4_16 : subd16_4 [1, 0] = true := by decide +kernel
theorem subd16_4_17 : subd16_4 [1, 1] = true := by decide +kernel
theorem subd16_4_18 : subd16_4 [1, 2] = true := by decide +kernel
theorem subd16_4_19 : subd16_4 [2] = true := by decide +kernel
theorem sbd16_4_0 : ∀ q ∈ blkd16_4_0, subd16_4 q = true := by
  unfold blkd16_4_0
  exact List.forall_mem_cons.2 ⟨subd16_4_0, List.forall_mem_cons.2 ⟨subd16_4_1, List.forall_mem_cons.2 ⟨subd16_4_2, List.forall_mem_cons.2 ⟨subd16_4_3, List.forall_mem_cons.2 ⟨subd16_4_4, List.forall_mem_cons.2 ⟨subd16_4_5, List.forall_mem_cons.2 ⟨subd16_4_6, List.forall_mem_cons.2 ⟨subd16_4_7, List.forall_mem_cons.2 ⟨subd16_4_8, List.forall_mem_cons.2 ⟨subd16_4_9, List.forall_mem_cons.2 ⟨subd16_4_10, List.forall_mem_cons.2 ⟨subd16_4_11, List.forall_mem_cons.2 ⟨subd16_4_12, List.forall_mem_cons.2 ⟨subd16_4_13, List.forall_mem_cons.2 ⟨subd16_4_14, List.forall_mem_cons.2 ⟨subd16_4_15, List.forall_mem_cons.2 ⟨subd16_4_16, List.forall_mem_cons.2 ⟨subd16_4_17, List.forall_mem_cons.2 ⟨subd16_4_18, List.forall_mem_cons.2 ⟨subd16_4_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_5 : ldCheck G d16_5.U d16_5.ms ldd16_5 = true := by decide +kernel
theorem pre_okd16_5 : subPre G cell16 d16_5 = true := by decide +kernel
theorem subd16_5_0 : subd16_5 [-1] = true := by decide +kernel
theorem subd16_5_1 : subd16_5 [0] = true := by decide +kernel
theorem subd16_5_2 : subd16_5 [1] = true := by decide +kernel
theorem sbd16_5_0 : ∀ q ∈ blkd16_5_0, subd16_5 q = true := by
  unfold blkd16_5_0
  exact List.forall_mem_cons.2 ⟨subd16_5_0, List.forall_mem_cons.2 ⟨subd16_5_1, List.forall_mem_cons.2 ⟨subd16_5_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
