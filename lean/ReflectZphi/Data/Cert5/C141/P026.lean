import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_1_0 : subd15_1 [-2] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-1] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [0] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [1] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [2] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-4] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [-3] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [-2, -4] = true := by decide +kernel
theorem subd15_2_3 : subd15_2 [-2, -3] = true := by decide +kernel
theorem subd15_2_4 : subd15_2 [-2, -2] = true := by decide +kernel
theorem subd15_2_5 : subd15_2 [-2, -1] = true := by decide +kernel
theorem subd15_2_6 : subd15_2 [-2, 0] = true := by decide +kernel
theorem subd15_2_7 : subd15_2 [-2, 1] = true := by decide +kernel
theorem subd15_2_8 : subd15_2 [-2, 2] = true := by decide +kernel
theorem subd15_2_9 : subd15_2 [-2, 3] = true := by decide +kernel
theorem subd15_2_10 : subd15_2 [-1, -5] = true := by decide +kernel
theorem subd15_2_11 : subd15_2 [-1, -4] = true := by decide +kernel
theorem subd15_2_12 : subd15_2 [-1, -3] = true := by decide +kernel
theorem subd15_2_13 : subd15_2 [-1, -2] = true := by decide +kernel
theorem subd15_2_14 : subd15_2 [-1, -1] = true := by decide +kernel
theorem subd15_2_15 : subd15_2 [-1, 0] = true := by decide +kernel
theorem subd15_2_16 : subd15_2 [-1, 1] = true := by decide +kernel
theorem subd15_2_17 : subd15_2 [-1, 2] = true := by decide +kernel
theorem subd15_2_18 : subd15_2 [-1, 3] = true := by decide +kernel
theorem subd15_2_19 : subd15_2 [0, -5] = true := by decide +kernel
theorem subd15_2_20 : subd15_2 [0, -4] = true := by decide +kernel
theorem subd15_2_21 : subd15_2 [0, -3] = true := by decide +kernel
theorem subd15_2_22 : subd15_2 [0, -2] = true := by decide +kernel
theorem subd15_2_23 : subd15_2 [0, -1] = true := by decide +kernel
theorem subd15_2_24 : subd15_2 [0, 0] = true := by decide +kernel
theorem subd15_2_25 : subd15_2 [0, 1] = true := by decide +kernel
theorem subd15_2_26 : subd15_2 [0, 2] = true := by decide +kernel
theorem subd15_2_27 : subd15_2 [0, 3] = true := by decide +kernel
theorem subd15_2_28 : subd15_2 [0, 4] = true := by decide +kernel
theorem subd15_2_29 : subd15_2 [1, -4] = true := by decide +kernel
theorem subd15_2_30 : subd15_2 [1, -3] = true := by decide +kernel
theorem subd15_2_31 : subd15_2 [1, -2] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_cons.2 ⟨subd15_2_3, List.forall_mem_cons.2 ⟨subd15_2_4, List.forall_mem_cons.2 ⟨subd15_2_5, List.forall_mem_cons.2 ⟨subd15_2_6, List.forall_mem_cons.2 ⟨subd15_2_7, List.forall_mem_cons.2 ⟨subd15_2_8, List.forall_mem_cons.2 ⟨subd15_2_9, List.forall_mem_cons.2 ⟨subd15_2_10, List.forall_mem_cons.2 ⟨subd15_2_11, List.forall_mem_cons.2 ⟨subd15_2_12, List.forall_mem_cons.2 ⟨subd15_2_13, List.forall_mem_cons.2 ⟨subd15_2_14, List.forall_mem_cons.2 ⟨subd15_2_15, List.forall_mem_cons.2 ⟨subd15_2_16, List.forall_mem_cons.2 ⟨subd15_2_17, List.forall_mem_cons.2 ⟨subd15_2_18, List.forall_mem_cons.2 ⟨subd15_2_19, List.forall_mem_cons.2 ⟨subd15_2_20, List.forall_mem_cons.2 ⟨subd15_2_21, List.forall_mem_cons.2 ⟨subd15_2_22, List.forall_mem_cons.2 ⟨subd15_2_23, List.forall_mem_cons.2 ⟨subd15_2_24, List.forall_mem_cons.2 ⟨subd15_2_25, List.forall_mem_cons.2 ⟨subd15_2_26, List.forall_mem_cons.2 ⟨subd15_2_27, List.forall_mem_cons.2 ⟨subd15_2_28, List.forall_mem_cons.2 ⟨subd15_2_29, List.forall_mem_cons.2 ⟨subd15_2_30, List.forall_mem_cons.2 ⟨subd15_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_32 : subd15_2 [1, -1] = true := by decide +kernel
theorem subd15_2_33 : subd15_2 [1, 0] = true := by decide +kernel
theorem subd15_2_34 : subd15_2 [1, 1] = true := by decide +kernel
theorem subd15_2_35 : subd15_2 [1, 2] = true := by decide +kernel
theorem subd15_2_36 : subd15_2 [1, 3] = true := by decide +kernel
theorem subd15_2_37 : subd15_2 [1, 4] = true := by decide +kernel
theorem subd15_2_38 : subd15_2 [2, -4] = true := by decide +kernel
theorem subd15_2_39 : subd15_2 [2, -3] = true := by decide +kernel
theorem subd15_2_40 : subd15_2 [2, -2] = true := by decide +kernel
theorem subd15_2_41 : subd15_2 [2, -1] = true := by decide +kernel
theorem subd15_2_42 : subd15_2 [2, 0] = true := by decide +kernel
theorem subd15_2_43 : subd15_2 [2, 1] = true := by decide +kernel
theorem subd15_2_44 : subd15_2 [2, 2] = true := by decide +kernel
theorem subd15_2_45 : subd15_2 [2, 3] = true := by decide +kernel
theorem subd15_2_46 : subd15_2 [3] = true := by decide +kernel
theorem subd15_2_47 : subd15_2 [4] = true := by decide +kernel
theorem sbd15_2_1 : ∀ q ∈ blkd15_2_1, subd15_2 q = true := by
  unfold blkd15_2_1
  exact List.forall_mem_cons.2 ⟨subd15_2_32, List.forall_mem_cons.2 ⟨subd15_2_33, List.forall_mem_cons.2 ⟨subd15_2_34, List.forall_mem_cons.2 ⟨subd15_2_35, List.forall_mem_cons.2 ⟨subd15_2_36, List.forall_mem_cons.2 ⟨subd15_2_37, List.forall_mem_cons.2 ⟨subd15_2_38, List.forall_mem_cons.2 ⟨subd15_2_39, List.forall_mem_cons.2 ⟨subd15_2_40, List.forall_mem_cons.2 ⟨subd15_2_41, List.forall_mem_cons.2 ⟨subd15_2_42, List.forall_mem_cons.2 ⟨subd15_2_43, List.forall_mem_cons.2 ⟨subd15_2_44, List.forall_mem_cons.2 ⟨subd15_2_45, List.forall_mem_cons.2 ⟨subd15_2_46, List.forall_mem_cons.2 ⟨subd15_2_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [-1] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [0] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [1] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [-3] = true := by decide +kernel
theorem subd16_0_1 : subd16_0 [-2, -4] = true := by decide +kernel
theorem subd16_0_2 : subd16_0 [-2, -3] = true := by decide +kernel
theorem subd16_0_3 : subd16_0 [-2, -2] = true := by decide +kernel
theorem subd16_0_4 : subd16_0 [-2, -1] = true := by decide +kernel
theorem subd16_0_5 : subd16_0 [-2, 0] = true := by decide +kernel
theorem subd16_0_6 : subd16_0 [-2, 1] = true := by decide +kernel
theorem subd16_0_7 : subd16_0 [-2, 2] = true := by decide +kernel
theorem subd16_0_8 : subd16_0 [-1, -4] = true := by decide +kernel
theorem subd16_0_9 : subd16_0 [-1, -3] = true := by decide +kernel
theorem subd16_0_10 : subd16_0 [-1, -2] = true := by decide +kernel
theorem subd16_0_11 : subd16_0 [-1, -1] = true := by decide +kernel
theorem subd16_0_12 : subd16_0 [-1, 0] = true := by decide +kernel
theorem subd16_0_13 : subd16_0 [-1, 1] = true := by decide +kernel
theorem subd16_0_14 : subd16_0 [-1, 2] = true := by decide +kernel
theorem subd16_0_15 : subd16_0 [0, -4] = true := by decide +kernel
theorem subd16_0_16 : subd16_0 [0, -3] = true := by decide +kernel
theorem subd16_0_17 : subd16_0 [0, -2] = true := by decide +kernel
theorem subd16_0_18 : subd16_0 [0, -1] = true := by decide +kernel
theorem subd16_0_19 : subd16_0 [0, 0] = true := by decide +kernel
theorem subd16_0_20 : subd16_0 [0, 1] = true := by decide +kernel
theorem subd16_0_21 : subd16_0 [0, 2] = true := by decide +kernel
theorem subd16_0_22 : subd16_0 [0, 3] = true := by decide +kernel
theorem subd16_0_23 : subd16_0 [1, -3] = true := by decide +kernel
theorem subd16_0_24 : subd16_0 [1, -2] = true := by decide +kernel
theorem subd16_0_25 : subd16_0 [1, -1] = true := by decide +kernel
theorem subd16_0_26 : subd16_0 [1, 0] = true := by decide +kernel
theorem subd16_0_27 : subd16_0 [1, 1] = true := by decide +kernel
theorem subd16_0_28 : subd16_0 [1, 2] = true := by decide +kernel
theorem subd16_0_29 : subd16_0 [1, 3] = true := by decide +kernel
theorem subd16_0_30 : subd16_0 [2, -3] = true := by decide +kernel
theorem subd16_0_31 : subd16_0 [2, -2] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_cons.2 ⟨subd16_0_1, List.forall_mem_cons.2 ⟨subd16_0_2, List.forall_mem_cons.2 ⟨subd16_0_3, List.forall_mem_cons.2 ⟨subd16_0_4, List.forall_mem_cons.2 ⟨subd16_0_5, List.forall_mem_cons.2 ⟨subd16_0_6, List.forall_mem_cons.2 ⟨subd16_0_7, List.forall_mem_cons.2 ⟨subd16_0_8, List.forall_mem_cons.2 ⟨subd16_0_9, List.forall_mem_cons.2 ⟨subd16_0_10, List.forall_mem_cons.2 ⟨subd16_0_11, List.forall_mem_cons.2 ⟨subd16_0_12, List.forall_mem_cons.2 ⟨subd16_0_13, List.forall_mem_cons.2 ⟨subd16_0_14, List.forall_mem_cons.2 ⟨subd16_0_15, List.forall_mem_cons.2 ⟨subd16_0_16, List.forall_mem_cons.2 ⟨subd16_0_17, List.forall_mem_cons.2 ⟨subd16_0_18, List.forall_mem_cons.2 ⟨subd16_0_19, List.forall_mem_cons.2 ⟨subd16_0_20, List.forall_mem_cons.2 ⟨subd16_0_21, List.forall_mem_cons.2 ⟨subd16_0_22, List.forall_mem_cons.2 ⟨subd16_0_23, List.forall_mem_cons.2 ⟨subd16_0_24, List.forall_mem_cons.2 ⟨subd16_0_25, List.forall_mem_cons.2 ⟨subd16_0_26, List.forall_mem_cons.2 ⟨subd16_0_27, List.forall_mem_cons.2 ⟨subd16_0_28, List.forall_mem_cons.2 ⟨subd16_0_29, List.forall_mem_cons.2 ⟨subd16_0_30, List.forall_mem_cons.2 ⟨subd16_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_0_32 : subd16_0 [2, -1] = true := by decide +kernel
theorem subd16_0_33 : subd16_0 [2, 0] = true := by decide +kernel
theorem subd16_0_34 : subd16_0 [2, 1] = true := by decide +kernel
theorem subd16_0_35 : subd16_0 [2, 2] = true := by decide +kernel
theorem subd16_0_36 : subd16_0 [2, 3] = true := by decide +kernel
theorem subd16_0_37 : subd16_0 [3] = true := by decide +kernel
theorem sbd16_0_1 : ∀ q ∈ blkd16_0_1, subd16_0 q = true := by
  unfold blkd16_0_1
  exact List.forall_mem_cons.2 ⟨subd16_0_32, List.forall_mem_cons.2 ⟨subd16_0_33, List.forall_mem_cons.2 ⟨subd16_0_34, List.forall_mem_cons.2 ⟨subd16_0_35, List.forall_mem_cons.2 ⟨subd16_0_36, List.forall_mem_cons.2 ⟨subd16_0_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-2] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-1] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [0] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [2] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
