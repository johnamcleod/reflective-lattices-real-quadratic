import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd19_2 : ldCheck G d19_2.U d19_2.ms ldd19_2 = true := by decide +kernel
theorem pre_okd19_2 : subPre G cell19 d19_2 = true := by decide +kernel
theorem subd19_2_0 : subd19_2 [-3] = true := by decide +kernel
theorem subd19_2_1 : subd19_2 [-2, -4] = true := by decide +kernel
theorem subd19_2_2 : subd19_2 [-2, -3] = true := by decide +kernel
theorem subd19_2_3 : subd19_2 [-2, -2] = true := by decide +kernel
theorem subd19_2_4 : subd19_2 [-2, -1] = true := by decide +kernel
theorem subd19_2_5 : subd19_2 [-2, 0] = true := by decide +kernel
theorem subd19_2_6 : subd19_2 [-2, 1] = true := by decide +kernel
theorem subd19_2_7 : subd19_2 [-2, 2] = true := by decide +kernel
theorem subd19_2_8 : subd19_2 [-2, 3] = true := by decide +kernel
theorem subd19_2_9 : subd19_2 [-2, 4] = true := by decide +kernel
theorem subd19_2_10 : subd19_2 [-1, -5] = true := by decide +kernel
theorem subd19_2_11 : subd19_2 [-1, -4] = true := by decide +kernel
theorem subd19_2_12 : subd19_2 [-1, -3] = true := by decide +kernel
theorem subd19_2_13 : subd19_2 [-1, -2] = true := by decide +kernel
theorem subd19_2_14 : subd19_2 [-1, -1] = true := by decide +kernel
theorem subd19_2_15 : subd19_2 [-1, 0] = true := by decide +kernel
theorem subd19_2_16 : subd19_2 [-1, 1] = true := by decide +kernel
theorem subd19_2_17 : subd19_2 [-1, 2] = true := by decide +kernel
theorem subd19_2_18 : subd19_2 [-1, 3] = true := by decide +kernel
theorem subd19_2_19 : subd19_2 [-1, 4] = true := by decide +kernel
theorem subd19_2_20 : subd19_2 [0, -5] = true := by decide +kernel
theorem subd19_2_21 : subd19_2 [0, -4] = true := by decide +kernel
theorem subd19_2_22 : subd19_2 [0, -3] = true := by decide +kernel
theorem subd19_2_23 : subd19_2 [0, -2] = true := by decide +kernel
theorem subd19_2_24 : subd19_2 [0, -1] = true := by decide +kernel
theorem subd19_2_25 : subd19_2 [0, 0] = true := by decide +kernel
theorem subd19_2_26 : subd19_2 [0, 1] = true := by decide +kernel
theorem subd19_2_27 : subd19_2 [0, 2] = true := by decide +kernel
theorem subd19_2_28 : subd19_2 [0, 3] = true := by decide +kernel
theorem subd19_2_29 : subd19_2 [0, 4] = true := by decide +kernel
theorem subd19_2_30 : subd19_2 [1, -5] = true := by decide +kernel
theorem subd19_2_31 : subd19_2 [1, -4] = true := by decide +kernel
theorem sbd19_2_0 : ∀ q ∈ blkd19_2_0, subd19_2 q = true := by
  unfold blkd19_2_0
  exact List.forall_mem_cons.2 ⟨subd19_2_0, List.forall_mem_cons.2 ⟨subd19_2_1, List.forall_mem_cons.2 ⟨subd19_2_2, List.forall_mem_cons.2 ⟨subd19_2_3, List.forall_mem_cons.2 ⟨subd19_2_4, List.forall_mem_cons.2 ⟨subd19_2_5, List.forall_mem_cons.2 ⟨subd19_2_6, List.forall_mem_cons.2 ⟨subd19_2_7, List.forall_mem_cons.2 ⟨subd19_2_8, List.forall_mem_cons.2 ⟨subd19_2_9, List.forall_mem_cons.2 ⟨subd19_2_10, List.forall_mem_cons.2 ⟨subd19_2_11, List.forall_mem_cons.2 ⟨subd19_2_12, List.forall_mem_cons.2 ⟨subd19_2_13, List.forall_mem_cons.2 ⟨subd19_2_14, List.forall_mem_cons.2 ⟨subd19_2_15, List.forall_mem_cons.2 ⟨subd19_2_16, List.forall_mem_cons.2 ⟨subd19_2_17, List.forall_mem_cons.2 ⟨subd19_2_18, List.forall_mem_cons.2 ⟨subd19_2_19, List.forall_mem_cons.2 ⟨subd19_2_20, List.forall_mem_cons.2 ⟨subd19_2_21, List.forall_mem_cons.2 ⟨subd19_2_22, List.forall_mem_cons.2 ⟨subd19_2_23, List.forall_mem_cons.2 ⟨subd19_2_24, List.forall_mem_cons.2 ⟨subd19_2_25, List.forall_mem_cons.2 ⟨subd19_2_26, List.forall_mem_cons.2 ⟨subd19_2_27, List.forall_mem_cons.2 ⟨subd19_2_28, List.forall_mem_cons.2 ⟨subd19_2_29, List.forall_mem_cons.2 ⟨subd19_2_30, List.forall_mem_cons.2 ⟨subd19_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_32 : subd19_2 [1, -3] = true := by decide +kernel
theorem subd19_2_33 : subd19_2 [1, -2] = true := by decide +kernel
theorem subd19_2_34 : subd19_2 [1, -1] = true := by decide +kernel
theorem subd19_2_35 : subd19_2 [1, 0] = true := by decide +kernel
theorem subd19_2_36 : subd19_2 [1, 1] = true := by decide +kernel
theorem subd19_2_37 : subd19_2 [1, 2] = true := by decide +kernel
theorem subd19_2_38 : subd19_2 [1, 3] = true := by decide +kernel
theorem subd19_2_39 : subd19_2 [1, 4] = true := by decide +kernel
theorem subd19_2_40 : subd19_2 [2, -5] = true := by decide +kernel
theorem subd19_2_41 : subd19_2 [2, -4] = true := by decide +kernel
theorem subd19_2_42 : subd19_2 [2, -3] = true := by decide +kernel
theorem subd19_2_43 : subd19_2 [2, -2] = true := by decide +kernel
theorem subd19_2_44 : subd19_2 [2, -1] = true := by decide +kernel
theorem subd19_2_45 : subd19_2 [2, 0] = true := by decide +kernel
theorem subd19_2_46 : subd19_2 [2, 1] = true := by decide +kernel
theorem subd19_2_47 : subd19_2 [2, 2] = true := by decide +kernel
theorem subd19_2_48 : subd19_2 [2, 3] = true := by decide +kernel
theorem subd19_2_49 : subd19_2 [3] = true := by decide +kernel
theorem sbd19_2_1 : ∀ q ∈ blkd19_2_1, subd19_2 q = true := by
  unfold blkd19_2_1
  exact List.forall_mem_cons.2 ⟨subd19_2_32, List.forall_mem_cons.2 ⟨subd19_2_33, List.forall_mem_cons.2 ⟨subd19_2_34, List.forall_mem_cons.2 ⟨subd19_2_35, List.forall_mem_cons.2 ⟨subd19_2_36, List.forall_mem_cons.2 ⟨subd19_2_37, List.forall_mem_cons.2 ⟨subd19_2_38, List.forall_mem_cons.2 ⟨subd19_2_39, List.forall_mem_cons.2 ⟨subd19_2_40, List.forall_mem_cons.2 ⟨subd19_2_41, List.forall_mem_cons.2 ⟨subd19_2_42, List.forall_mem_cons.2 ⟨subd19_2_43, List.forall_mem_cons.2 ⟨subd19_2_44, List.forall_mem_cons.2 ⟨subd19_2_45, List.forall_mem_cons.2 ⟨subd19_2_46, List.forall_mem_cons.2 ⟨subd19_2_47, List.forall_mem_cons.2 ⟨subd19_2_48, List.forall_mem_cons.2 ⟨subd19_2_49, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_3 : ldCheck G d19_3.U d19_3.ms ldd19_3 = true := by decide +kernel
theorem pre_okd19_3 : subPre G cell19 d19_3 = true := by decide +kernel
theorem subd19_3_0 : subd19_3 [] = true := by decide +kernel
theorem sbd19_3_0 : ∀ q ∈ blkd19_3_0, subd19_3 q = true := by
  unfold blkd19_3_0
  exact List.forall_mem_cons.2 ⟨subd19_3_0, List.forall_mem_nil _⟩
theorem ld_okd20_0 : ldCheck G d20_0.U d20_0.ms ldd20_0 = true := by decide +kernel
theorem pre_okd20_0 : subPre G cell20 d20_0 = true := by decide +kernel
theorem subd20_0_0 : subd20_0 [] = true := by decide +kernel
theorem sbd20_0_0 : ∀ q ∈ blkd20_0_0, subd20_0 q = true := by
  unfold blkd20_0_0
  exact List.forall_mem_cons.2 ⟨subd20_0_0, List.forall_mem_nil _⟩
theorem ld_okd20_1 : ldCheck G d20_1.U d20_1.ms ldd20_1 = true := by decide +kernel
theorem pre_okd20_1 : subPre G cell20 d20_1 = true := by decide +kernel
theorem subd20_1_0 : subd20_1 [] = true := by decide +kernel
theorem sbd20_1_0 : ∀ q ∈ blkd20_1_0, subd20_1 q = true := by
  unfold blkd20_1_0
  exact List.forall_mem_cons.2 ⟨subd20_1_0, List.forall_mem_nil _⟩
theorem ld_okd20_2 : ldCheck G d20_2.U d20_2.ms ldd20_2 = true := by decide +kernel
theorem pre_okd20_2 : subPre G cell20 d20_2 = true := by decide +kernel
theorem subd20_2_0 : subd20_2 [-2] = true := by decide +kernel
theorem subd20_2_1 : subd20_2 [-1, -4] = true := by decide +kernel
theorem subd20_2_2 : subd20_2 [-1, -3] = true := by decide +kernel
theorem subd20_2_3 : subd20_2 [-1, -2] = true := by decide +kernel
theorem subd20_2_4 : subd20_2 [-1, -1] = true := by decide +kernel
theorem subd20_2_5 : subd20_2 [-1, 0] = true := by decide +kernel
theorem subd20_2_6 : subd20_2 [-1, 1] = true := by decide +kernel
theorem subd20_2_7 : subd20_2 [-1, 2] = true := by decide +kernel
theorem subd20_2_8 : subd20_2 [0, -4] = true := by decide +kernel
theorem subd20_2_9 : subd20_2 [0, -3] = true := by decide +kernel
theorem subd20_2_10 : subd20_2 [0, -2] = true := by decide +kernel
theorem subd20_2_11 : subd20_2 [0, -1] = true := by decide +kernel
theorem subd20_2_12 : subd20_2 [0, 0] = true := by decide +kernel
theorem subd20_2_13 : subd20_2 [0, 1] = true := by decide +kernel
theorem subd20_2_14 : subd20_2 [0, 2] = true := by decide +kernel
theorem subd20_2_15 : subd20_2 [0, 3] = true := by decide +kernel
theorem subd20_2_16 : subd20_2 [1, -3] = true := by decide +kernel
theorem subd20_2_17 : subd20_2 [1, -2] = true := by decide +kernel
theorem subd20_2_18 : subd20_2 [1, -1] = true := by decide +kernel
theorem subd20_2_19 : subd20_2 [1, 0] = true := by decide +kernel
theorem subd20_2_20 : subd20_2 [1, 1] = true := by decide +kernel
theorem subd20_2_21 : subd20_2 [1, 2] = true := by decide +kernel
theorem subd20_2_22 : subd20_2 [1, 3] = true := by decide +kernel
theorem subd20_2_23 : subd20_2 [2] = true := by decide +kernel
theorem sbd20_2_0 : ∀ q ∈ blkd20_2_0, subd20_2 q = true := by
  unfold blkd20_2_0
  exact List.forall_mem_cons.2 ⟨subd20_2_0, List.forall_mem_cons.2 ⟨subd20_2_1, List.forall_mem_cons.2 ⟨subd20_2_2, List.forall_mem_cons.2 ⟨subd20_2_3, List.forall_mem_cons.2 ⟨subd20_2_4, List.forall_mem_cons.2 ⟨subd20_2_5, List.forall_mem_cons.2 ⟨subd20_2_6, List.forall_mem_cons.2 ⟨subd20_2_7, List.forall_mem_cons.2 ⟨subd20_2_8, List.forall_mem_cons.2 ⟨subd20_2_9, List.forall_mem_cons.2 ⟨subd20_2_10, List.forall_mem_cons.2 ⟨subd20_2_11, List.forall_mem_cons.2 ⟨subd20_2_12, List.forall_mem_cons.2 ⟨subd20_2_13, List.forall_mem_cons.2 ⟨subd20_2_14, List.forall_mem_cons.2 ⟨subd20_2_15, List.forall_mem_cons.2 ⟨subd20_2_16, List.forall_mem_cons.2 ⟨subd20_2_17, List.forall_mem_cons.2 ⟨subd20_2_18, List.forall_mem_cons.2 ⟨subd20_2_19, List.forall_mem_cons.2 ⟨subd20_2_20, List.forall_mem_cons.2 ⟨subd20_2_21, List.forall_mem_cons.2 ⟨subd20_2_22, List.forall_mem_cons.2 ⟨subd20_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd20_3 : ldCheck G d20_3.U d20_3.ms ldd20_3 = true := by decide +kernel
theorem pre_okd20_3 : subPre G cell20 d20_3 = true := by decide +kernel
theorem subd20_3_0 : subd20_3 [] = true := by decide +kernel
theorem sbd20_3_0 : ∀ q ∈ blkd20_3_0, subd20_3 q = true := by
  unfold blkd20_3_0
  exact List.forall_mem_cons.2 ⟨subd20_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C142
