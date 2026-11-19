import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd15_11 : ldCheck G d15_11.U d15_11.ms ldd15_11 = true := by decide +kernel
theorem pre_okd15_11 : subPre G cell15 d15_11 = true := by decide +kernel
theorem subd15_11_0 : subd15_11 [] = true := by decide +kernel
theorem sbd15_11_0 : ∀ q ∈ blkd15_11_0, subd15_11 q = true := by
  unfold blkd15_11_0
  exact List.forall_mem_cons.2 ⟨subd15_11_0, List.forall_mem_nil _⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_nil _⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_nil _⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel
theorem subd16_2_0 : subd16_2 [] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_nil _⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_nil _⟩
theorem ld_okd16_4 : ldCheck G d16_4.U d16_4.ms ldd16_4 = true := by decide +kernel
theorem pre_okd16_4 : subPre G cell16 d16_4 = true := by decide +kernel
theorem subd16_4_0 : subd16_4 [-3] = true := by decide +kernel
theorem subd16_4_1 : subd16_4 [-2, -4] = true := by decide +kernel
theorem subd16_4_2 : subd16_4 [-2, -3] = true := by decide +kernel
theorem subd16_4_3 : subd16_4 [-2, -2] = true := by decide +kernel
theorem subd16_4_4 : subd16_4 [-2, -1] = true := by decide +kernel
theorem subd16_4_5 : subd16_4 [-2, 0] = true := by decide +kernel
theorem subd16_4_6 : subd16_4 [-2, 1] = true := by decide +kernel
theorem subd16_4_7 : subd16_4 [-2, 2] = true := by decide +kernel
theorem subd16_4_8 : subd16_4 [-2, 3] = true := by decide +kernel
theorem subd16_4_9 : subd16_4 [-1, -5] = true := by decide +kernel
theorem subd16_4_10 : subd16_4 [-1, -4] = true := by decide +kernel
theorem subd16_4_11 : subd16_4 [-1, -3] = true := by decide +kernel
theorem subd16_4_12 : subd16_4 [-1, -2] = true := by decide +kernel
theorem subd16_4_13 : subd16_4 [-1, -1] = true := by decide +kernel
theorem subd16_4_14 : subd16_4 [-1, 0] = true := by decide +kernel
theorem subd16_4_15 : subd16_4 [-1, 1] = true := by decide +kernel
theorem subd16_4_16 : subd16_4 [-1, 2] = true := by decide +kernel
theorem subd16_4_17 : subd16_4 [-1, 3] = true := by decide +kernel
theorem subd16_4_18 : subd16_4 [-1, 4] = true := by decide +kernel
theorem subd16_4_19 : subd16_4 [0, -5] = true := by decide +kernel
theorem subd16_4_20 : subd16_4 [0, -4] = true := by decide +kernel
theorem subd16_4_21 : subd16_4 [0, -3] = true := by decide +kernel
theorem subd16_4_22 : subd16_4 [0, -2] = true := by decide +kernel
theorem subd16_4_23 : subd16_4 [0, -1] = true := by decide +kernel
theorem subd16_4_24 : subd16_4 [0, 0] = true := by decide +kernel
theorem subd16_4_25 : subd16_4 [0, 1] = true := by decide +kernel
theorem subd16_4_26 : subd16_4 [0, 2] = true := by decide +kernel
theorem subd16_4_27 : subd16_4 [0, 3] = true := by decide +kernel
theorem subd16_4_28 : subd16_4 [0, 4] = true := by decide +kernel
theorem subd16_4_29 : subd16_4 [1, -5] = true := by decide +kernel
theorem subd16_4_30 : subd16_4 [1, -4] = true := by decide +kernel
theorem subd16_4_31 : subd16_4 [1, -3] = true := by decide +kernel
theorem sbd16_4_0 : ∀ q ∈ blkd16_4_0, subd16_4 q = true := by
  unfold blkd16_4_0
  exact List.forall_mem_cons.2 ⟨subd16_4_0, List.forall_mem_cons.2 ⟨subd16_4_1, List.forall_mem_cons.2 ⟨subd16_4_2, List.forall_mem_cons.2 ⟨subd16_4_3, List.forall_mem_cons.2 ⟨subd16_4_4, List.forall_mem_cons.2 ⟨subd16_4_5, List.forall_mem_cons.2 ⟨subd16_4_6, List.forall_mem_cons.2 ⟨subd16_4_7, List.forall_mem_cons.2 ⟨subd16_4_8, List.forall_mem_cons.2 ⟨subd16_4_9, List.forall_mem_cons.2 ⟨subd16_4_10, List.forall_mem_cons.2 ⟨subd16_4_11, List.forall_mem_cons.2 ⟨subd16_4_12, List.forall_mem_cons.2 ⟨subd16_4_13, List.forall_mem_cons.2 ⟨subd16_4_14, List.forall_mem_cons.2 ⟨subd16_4_15, List.forall_mem_cons.2 ⟨subd16_4_16, List.forall_mem_cons.2 ⟨subd16_4_17, List.forall_mem_cons.2 ⟨subd16_4_18, List.forall_mem_cons.2 ⟨subd16_4_19, List.forall_mem_cons.2 ⟨subd16_4_20, List.forall_mem_cons.2 ⟨subd16_4_21, List.forall_mem_cons.2 ⟨subd16_4_22, List.forall_mem_cons.2 ⟨subd16_4_23, List.forall_mem_cons.2 ⟨subd16_4_24, List.forall_mem_cons.2 ⟨subd16_4_25, List.forall_mem_cons.2 ⟨subd16_4_26, List.forall_mem_cons.2 ⟨subd16_4_27, List.forall_mem_cons.2 ⟨subd16_4_28, List.forall_mem_cons.2 ⟨subd16_4_29, List.forall_mem_cons.2 ⟨subd16_4_30, List.forall_mem_cons.2 ⟨subd16_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_4_32 : subd16_4 [1, -2] = true := by decide +kernel
theorem subd16_4_33 : subd16_4 [1, -1] = true := by decide +kernel
theorem subd16_4_34 : subd16_4 [1, 0] = true := by decide +kernel
theorem subd16_4_35 : subd16_4 [1, 1] = true := by decide +kernel
theorem subd16_4_36 : subd16_4 [1, 2] = true := by decide +kernel
theorem subd16_4_37 : subd16_4 [1, 3] = true := by decide +kernel
theorem subd16_4_38 : subd16_4 [1, 4] = true := by decide +kernel
theorem subd16_4_39 : subd16_4 [2, -4] = true := by decide +kernel
theorem subd16_4_40 : subd16_4 [2, -3] = true := by decide +kernel
theorem subd16_4_41 : subd16_4 [2, -2] = true := by decide +kernel
theorem subd16_4_42 : subd16_4 [2, -1] = true := by decide +kernel
theorem subd16_4_43 : subd16_4 [2, 0] = true := by decide +kernel
theorem subd16_4_44 : subd16_4 [2, 1] = true := by decide +kernel
theorem subd16_4_45 : subd16_4 [2, 2] = true := by decide +kernel
theorem subd16_4_46 : subd16_4 [2, 3] = true := by decide +kernel
theorem subd16_4_47 : subd16_4 [3] = true := by decide +kernel
theorem sbd16_4_1 : ∀ q ∈ blkd16_4_1, subd16_4 q = true := by
  unfold blkd16_4_1
  exact List.forall_mem_cons.2 ⟨subd16_4_32, List.forall_mem_cons.2 ⟨subd16_4_33, List.forall_mem_cons.2 ⟨subd16_4_34, List.forall_mem_cons.2 ⟨subd16_4_35, List.forall_mem_cons.2 ⟨subd16_4_36, List.forall_mem_cons.2 ⟨subd16_4_37, List.forall_mem_cons.2 ⟨subd16_4_38, List.forall_mem_cons.2 ⟨subd16_4_39, List.forall_mem_cons.2 ⟨subd16_4_40, List.forall_mem_cons.2 ⟨subd16_4_41, List.forall_mem_cons.2 ⟨subd16_4_42, List.forall_mem_cons.2 ⟨subd16_4_43, List.forall_mem_cons.2 ⟨subd16_4_44, List.forall_mem_cons.2 ⟨subd16_4_45, List.forall_mem_cons.2 ⟨subd16_4_46, List.forall_mem_cons.2 ⟨subd16_4_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_5 : ldCheck G d16_5.U d16_5.ms ldd16_5 = true := by decide +kernel
theorem pre_okd16_5 : subPre G cell16 d16_5 = true := by decide +kernel
theorem subd16_5_0 : subd16_5 [-2] = true := by decide +kernel
theorem subd16_5_1 : subd16_5 [-1] = true := by decide +kernel
theorem subd16_5_2 : subd16_5 [0] = true := by decide +kernel
theorem subd16_5_3 : subd16_5 [1] = true := by decide +kernel
theorem subd16_5_4 : subd16_5 [2] = true := by decide +kernel
theorem sbd16_5_0 : ∀ q ∈ blkd16_5_0, subd16_5 q = true := by
  unfold blkd16_5_0
  exact List.forall_mem_cons.2 ⟨subd16_5_0, List.forall_mem_cons.2 ⟨subd16_5_1, List.forall_mem_cons.2 ⟨subd16_5_2, List.forall_mem_cons.2 ⟨subd16_5_3, List.forall_mem_cons.2 ⟨subd16_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
