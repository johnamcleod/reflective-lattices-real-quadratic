import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_2_0 : subd16_2 [-3] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [-2, -3] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [-2, -2] = true := by decide +kernel
theorem subd16_2_3 : subd16_2 [-2, -1] = true := by decide +kernel
theorem subd16_2_4 : subd16_2 [-2, 0] = true := by decide +kernel
theorem subd16_2_5 : subd16_2 [-2, 1] = true := by decide +kernel
theorem subd16_2_6 : subd16_2 [-2, 2] = true := by decide +kernel
theorem subd16_2_7 : subd16_2 [-2, 3] = true := by decide +kernel
theorem subd16_2_8 : subd16_2 [-2, 4] = true := by decide +kernel
theorem subd16_2_9 : subd16_2 [-1, -4] = true := by decide +kernel
theorem subd16_2_10 : subd16_2 [-1, -3] = true := by decide +kernel
theorem subd16_2_11 : subd16_2 [-1, -2] = true := by decide +kernel
theorem subd16_2_12 : subd16_2 [-1, -1] = true := by decide +kernel
theorem subd16_2_13 : subd16_2 [-1, 0] = true := by decide +kernel
theorem subd16_2_14 : subd16_2 [-1, 1] = true := by decide +kernel
theorem subd16_2_15 : subd16_2 [-1, 2] = true := by decide +kernel
theorem subd16_2_16 : subd16_2 [-1, 3] = true := by decide +kernel
theorem subd16_2_17 : subd16_2 [-1, 4] = true := by decide +kernel
theorem subd16_2_18 : subd16_2 [0, -4] = true := by decide +kernel
theorem subd16_2_19 : subd16_2 [0, -3] = true := by decide +kernel
theorem subd16_2_20 : subd16_2 [0, -2] = true := by decide +kernel
theorem subd16_2_21 : subd16_2 [0, -1] = true := by decide +kernel
theorem subd16_2_22 : subd16_2 [0, 0] = true := by decide +kernel
theorem subd16_2_23 : subd16_2 [0, 1] = true := by decide +kernel
theorem subd16_2_24 : subd16_2 [0, 2] = true := by decide +kernel
theorem subd16_2_25 : subd16_2 [0, 3] = true := by decide +kernel
theorem subd16_2_26 : subd16_2 [1, -5] = true := by decide +kernel
theorem subd16_2_27 : subd16_2 [1, -4] = true := by decide +kernel
theorem subd16_2_28 : subd16_2 [1, -3] = true := by decide +kernel
theorem subd16_2_29 : subd16_2 [1, -2] = true := by decide +kernel
theorem subd16_2_30 : subd16_2 [1, -1] = true := by decide +kernel
theorem subd16_2_31 : subd16_2 [1, 0] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_cons.2 ⟨subd16_2_3, List.forall_mem_cons.2 ⟨subd16_2_4, List.forall_mem_cons.2 ⟨subd16_2_5, List.forall_mem_cons.2 ⟨subd16_2_6, List.forall_mem_cons.2 ⟨subd16_2_7, List.forall_mem_cons.2 ⟨subd16_2_8, List.forall_mem_cons.2 ⟨subd16_2_9, List.forall_mem_cons.2 ⟨subd16_2_10, List.forall_mem_cons.2 ⟨subd16_2_11, List.forall_mem_cons.2 ⟨subd16_2_12, List.forall_mem_cons.2 ⟨subd16_2_13, List.forall_mem_cons.2 ⟨subd16_2_14, List.forall_mem_cons.2 ⟨subd16_2_15, List.forall_mem_cons.2 ⟨subd16_2_16, List.forall_mem_cons.2 ⟨subd16_2_17, List.forall_mem_cons.2 ⟨subd16_2_18, List.forall_mem_cons.2 ⟨subd16_2_19, List.forall_mem_cons.2 ⟨subd16_2_20, List.forall_mem_cons.2 ⟨subd16_2_21, List.forall_mem_cons.2 ⟨subd16_2_22, List.forall_mem_cons.2 ⟨subd16_2_23, List.forall_mem_cons.2 ⟨subd16_2_24, List.forall_mem_cons.2 ⟨subd16_2_25, List.forall_mem_cons.2 ⟨subd16_2_26, List.forall_mem_cons.2 ⟨subd16_2_27, List.forall_mem_cons.2 ⟨subd16_2_28, List.forall_mem_cons.2 ⟨subd16_2_29, List.forall_mem_cons.2 ⟨subd16_2_30, List.forall_mem_cons.2 ⟨subd16_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_2_32 : subd16_2 [1, 1] = true := by decide +kernel
theorem subd16_2_33 : subd16_2 [1, 2] = true := by decide +kernel
theorem subd16_2_34 : subd16_2 [1, 3] = true := by decide +kernel
theorem subd16_2_35 : subd16_2 [2, -5] = true := by decide +kernel
theorem subd16_2_36 : subd16_2 [2, -4] = true := by decide +kernel
theorem subd16_2_37 : subd16_2 [2, -3] = true := by decide +kernel
theorem subd16_2_38 : subd16_2 [2, -2] = true := by decide +kernel
theorem subd16_2_39 : subd16_2 [2, -1] = true := by decide +kernel
theorem subd16_2_40 : subd16_2 [2, 0] = true := by decide +kernel
theorem subd16_2_41 : subd16_2 [2, 1] = true := by decide +kernel
theorem subd16_2_42 : subd16_2 [2, 2] = true := by decide +kernel
theorem subd16_2_43 : subd16_2 [3] = true := by decide +kernel
theorem sbd16_2_1 : ∀ q ∈ blkd16_2_1, subd16_2 q = true := by
  unfold blkd16_2_1
  exact List.forall_mem_cons.2 ⟨subd16_2_32, List.forall_mem_cons.2 ⟨subd16_2_33, List.forall_mem_cons.2 ⟨subd16_2_34, List.forall_mem_cons.2 ⟨subd16_2_35, List.forall_mem_cons.2 ⟨subd16_2_36, List.forall_mem_cons.2 ⟨subd16_2_37, List.forall_mem_cons.2 ⟨subd16_2_38, List.forall_mem_cons.2 ⟨subd16_2_39, List.forall_mem_cons.2 ⟨subd16_2_40, List.forall_mem_cons.2 ⟨subd16_2_41, List.forall_mem_cons.2 ⟨subd16_2_42, List.forall_mem_cons.2 ⟨subd16_2_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [-1] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [0] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [1] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [-3] = true := by decide +kernel
theorem subd17_0_1 : subd17_0 [-2] = true := by decide +kernel
theorem subd17_0_2 : subd17_0 [-1, -4] = true := by decide +kernel
theorem subd17_0_3 : subd17_0 [-1, -3] = true := by decide +kernel
theorem subd17_0_4 : subd17_0 [-1, -2] = true := by decide +kernel
theorem subd17_0_5 : subd17_0 [-1, -1] = true := by decide +kernel
theorem subd17_0_6 : subd17_0 [-1, 0] = true := by decide +kernel
theorem subd17_0_7 : subd17_0 [-1, 1] = true := by decide +kernel
theorem subd17_0_8 : subd17_0 [-1, 2] = true := by decide +kernel
theorem subd17_0_9 : subd17_0 [0, -3] = true := by decide +kernel
theorem subd17_0_10 : subd17_0 [0, -2] = true := by decide +kernel
theorem subd17_0_11 : subd17_0 [0, -1] = true := by decide +kernel
theorem subd17_0_12 : subd17_0 [0, 0] = true := by decide +kernel
theorem subd17_0_13 : subd17_0 [0, 1] = true := by decide +kernel
theorem subd17_0_14 : subd17_0 [0, 2] = true := by decide +kernel
theorem subd17_0_15 : subd17_0 [1, -3] = true := by decide +kernel
theorem subd17_0_16 : subd17_0 [1, -2] = true := by decide +kernel
theorem subd17_0_17 : subd17_0 [1, -1] = true := by decide +kernel
theorem subd17_0_18 : subd17_0 [1, 0] = true := by decide +kernel
theorem subd17_0_19 : subd17_0 [1, 1] = true := by decide +kernel
theorem subd17_0_20 : subd17_0 [1, 2] = true := by decide +kernel
theorem subd17_0_21 : subd17_0 [1, 3] = true := by decide +kernel
theorem subd17_0_22 : subd17_0 [2] = true := by decide +kernel
theorem subd17_0_23 : subd17_0 [3] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_cons.2 ⟨subd17_0_1, List.forall_mem_cons.2 ⟨subd17_0_2, List.forall_mem_cons.2 ⟨subd17_0_3, List.forall_mem_cons.2 ⟨subd17_0_4, List.forall_mem_cons.2 ⟨subd17_0_5, List.forall_mem_cons.2 ⟨subd17_0_6, List.forall_mem_cons.2 ⟨subd17_0_7, List.forall_mem_cons.2 ⟨subd17_0_8, List.forall_mem_cons.2 ⟨subd17_0_9, List.forall_mem_cons.2 ⟨subd17_0_10, List.forall_mem_cons.2 ⟨subd17_0_11, List.forall_mem_cons.2 ⟨subd17_0_12, List.forall_mem_cons.2 ⟨subd17_0_13, List.forall_mem_cons.2 ⟨subd17_0_14, List.forall_mem_cons.2 ⟨subd17_0_15, List.forall_mem_cons.2 ⟨subd17_0_16, List.forall_mem_cons.2 ⟨subd17_0_17, List.forall_mem_cons.2 ⟨subd17_0_18, List.forall_mem_cons.2 ⟨subd17_0_19, List.forall_mem_cons.2 ⟨subd17_0_20, List.forall_mem_cons.2 ⟨subd17_0_21, List.forall_mem_cons.2 ⟨subd17_0_22, List.forall_mem_cons.2 ⟨subd17_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [-2] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-1] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [0] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [1] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [2] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel
theorem subd17_2_0 : subd17_2 [-3] = true := by decide +kernel
theorem subd17_2_1 : subd17_2 [-2, -3] = true := by decide +kernel
theorem subd17_2_2 : subd17_2 [-2, -2] = true := by decide +kernel
theorem subd17_2_3 : subd17_2 [-2, -1] = true := by decide +kernel
theorem subd17_2_4 : subd17_2 [-2, 0] = true := by decide +kernel
theorem subd17_2_5 : subd17_2 [-2, 1] = true := by decide +kernel
theorem subd17_2_6 : subd17_2 [-2, 2] = true := by decide +kernel
theorem subd17_2_7 : subd17_2 [-2, 3] = true := by decide +kernel
theorem subd17_2_8 : subd17_2 [-1, -3] = true := by decide +kernel
theorem subd17_2_9 : subd17_2 [-1, -2] = true := by decide +kernel
theorem subd17_2_10 : subd17_2 [-1, -1] = true := by decide +kernel
theorem subd17_2_11 : subd17_2 [-1, 0] = true := by decide +kernel
theorem subd17_2_12 : subd17_2 [-1, 1] = true := by decide +kernel
theorem subd17_2_13 : subd17_2 [-1, 2] = true := by decide +kernel
theorem subd17_2_14 : subd17_2 [-1, 3] = true := by decide +kernel
theorem subd17_2_15 : subd17_2 [0, -4] = true := by decide +kernel
theorem subd17_2_16 : subd17_2 [0, -3] = true := by decide +kernel
theorem subd17_2_17 : subd17_2 [0, -2] = true := by decide +kernel
theorem subd17_2_18 : subd17_2 [0, -1] = true := by decide +kernel
theorem subd17_2_19 : subd17_2 [0, 0] = true := by decide +kernel
theorem subd17_2_20 : subd17_2 [0, 1] = true := by decide +kernel
theorem subd17_2_21 : subd17_2 [0, 2] = true := by decide +kernel
theorem subd17_2_22 : subd17_2 [0, 3] = true := by decide +kernel
theorem subd17_2_23 : subd17_2 [1, -4] = true := by decide +kernel
theorem subd17_2_24 : subd17_2 [1, -3] = true := by decide +kernel
theorem subd17_2_25 : subd17_2 [1, -2] = true := by decide +kernel
theorem subd17_2_26 : subd17_2 [1, -1] = true := by decide +kernel
theorem subd17_2_27 : subd17_2 [1, 0] = true := by decide +kernel
theorem subd17_2_28 : subd17_2 [1, 1] = true := by decide +kernel
theorem subd17_2_29 : subd17_2 [1, 2] = true := by decide +kernel
theorem subd17_2_30 : subd17_2 [2, -4] = true := by decide +kernel
theorem subd17_2_31 : subd17_2 [2, -3] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_cons.2 ⟨subd17_2_1, List.forall_mem_cons.2 ⟨subd17_2_2, List.forall_mem_cons.2 ⟨subd17_2_3, List.forall_mem_cons.2 ⟨subd17_2_4, List.forall_mem_cons.2 ⟨subd17_2_5, List.forall_mem_cons.2 ⟨subd17_2_6, List.forall_mem_cons.2 ⟨subd17_2_7, List.forall_mem_cons.2 ⟨subd17_2_8, List.forall_mem_cons.2 ⟨subd17_2_9, List.forall_mem_cons.2 ⟨subd17_2_10, List.forall_mem_cons.2 ⟨subd17_2_11, List.forall_mem_cons.2 ⟨subd17_2_12, List.forall_mem_cons.2 ⟨subd17_2_13, List.forall_mem_cons.2 ⟨subd17_2_14, List.forall_mem_cons.2 ⟨subd17_2_15, List.forall_mem_cons.2 ⟨subd17_2_16, List.forall_mem_cons.2 ⟨subd17_2_17, List.forall_mem_cons.2 ⟨subd17_2_18, List.forall_mem_cons.2 ⟨subd17_2_19, List.forall_mem_cons.2 ⟨subd17_2_20, List.forall_mem_cons.2 ⟨subd17_2_21, List.forall_mem_cons.2 ⟨subd17_2_22, List.forall_mem_cons.2 ⟨subd17_2_23, List.forall_mem_cons.2 ⟨subd17_2_24, List.forall_mem_cons.2 ⟨subd17_2_25, List.forall_mem_cons.2 ⟨subd17_2_26, List.forall_mem_cons.2 ⟨subd17_2_27, List.forall_mem_cons.2 ⟨subd17_2_28, List.forall_mem_cons.2 ⟨subd17_2_29, List.forall_mem_cons.2 ⟨subd17_2_30, List.forall_mem_cons.2 ⟨subd17_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_32 : subd17_2 [2, -2] = true := by decide +kernel
theorem subd17_2_33 : subd17_2 [2, -1] = true := by decide +kernel
theorem subd17_2_34 : subd17_2 [2, 0] = true := by decide +kernel
theorem subd17_2_35 : subd17_2 [2, 1] = true := by decide +kernel
theorem subd17_2_36 : subd17_2 [2, 2] = true := by decide +kernel
theorem subd17_2_37 : subd17_2 [3] = true := by decide +kernel
theorem sbd17_2_1 : ∀ q ∈ blkd17_2_1, subd17_2 q = true := by
  unfold blkd17_2_1
  exact List.forall_mem_cons.2 ⟨subd17_2_32, List.forall_mem_cons.2 ⟨subd17_2_33, List.forall_mem_cons.2 ⟨subd17_2_34, List.forall_mem_cons.2 ⟨subd17_2_35, List.forall_mem_cons.2 ⟨subd17_2_36, List.forall_mem_cons.2 ⟨subd17_2_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
