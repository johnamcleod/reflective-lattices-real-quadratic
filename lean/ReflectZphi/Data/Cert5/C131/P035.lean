import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_1_0 : subd18_1 [-2] = true := by decide +kernel
theorem subd18_1_1 : subd18_1 [-1, -3] = true := by decide +kernel
theorem subd18_1_2 : subd18_1 [-1, -2] = true := by decide +kernel
theorem subd18_1_3 : subd18_1 [-1, -1] = true := by decide +kernel
theorem subd18_1_4 : subd18_1 [-1, 0] = true := by decide +kernel
theorem subd18_1_5 : subd18_1 [-1, 1] = true := by decide +kernel
theorem subd18_1_6 : subd18_1 [-1, 2] = true := by decide +kernel
theorem subd18_1_7 : subd18_1 [0, -3] = true := by decide +kernel
theorem subd18_1_8 : subd18_1 [0, -2] = true := by decide +kernel
theorem subd18_1_9 : subd18_1 [0, -1] = true := by decide +kernel
theorem subd18_1_10 : subd18_1 [0, 0] = true := by decide +kernel
theorem subd18_1_11 : subd18_1 [0, 1] = true := by decide +kernel
theorem subd18_1_12 : subd18_1 [0, 2] = true := by decide +kernel
theorem subd18_1_13 : subd18_1 [1, -3] = true := by decide +kernel
theorem subd18_1_14 : subd18_1 [1, -2] = true := by decide +kernel
theorem subd18_1_15 : subd18_1 [1, -1] = true := by decide +kernel
theorem subd18_1_16 : subd18_1 [1, 0] = true := by decide +kernel
theorem subd18_1_17 : subd18_1 [1, 1] = true := by decide +kernel
theorem subd18_1_18 : subd18_1 [1, 2] = true := by decide +kernel
theorem subd18_1_19 : subd18_1 [2] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_cons.2 ⟨subd18_1_1, List.forall_mem_cons.2 ⟨subd18_1_2, List.forall_mem_cons.2 ⟨subd18_1_3, List.forall_mem_cons.2 ⟨subd18_1_4, List.forall_mem_cons.2 ⟨subd18_1_5, List.forall_mem_cons.2 ⟨subd18_1_6, List.forall_mem_cons.2 ⟨subd18_1_7, List.forall_mem_cons.2 ⟨subd18_1_8, List.forall_mem_cons.2 ⟨subd18_1_9, List.forall_mem_cons.2 ⟨subd18_1_10, List.forall_mem_cons.2 ⟨subd18_1_11, List.forall_mem_cons.2 ⟨subd18_1_12, List.forall_mem_cons.2 ⟨subd18_1_13, List.forall_mem_cons.2 ⟨subd18_1_14, List.forall_mem_cons.2 ⟨subd18_1_15, List.forall_mem_cons.2 ⟨subd18_1_16, List.forall_mem_cons.2 ⟨subd18_1_17, List.forall_mem_cons.2 ⟨subd18_1_18, List.forall_mem_cons.2 ⟨subd18_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_0 : ldCheck G d19_0.U d19_0.ms ldd19_0 = true := by decide +kernel
theorem pre_okd19_0 : subPre G cell19 d19_0 = true := by decide +kernel
theorem subd19_0_0 : subd19_0 [-3] = true := by decide +kernel
theorem subd19_0_1 : subd19_0 [-2, -3] = true := by decide +kernel
theorem subd19_0_2 : subd19_0 [-2, -2] = true := by decide +kernel
theorem subd19_0_3 : subd19_0 [-2, -1] = true := by decide +kernel
theorem subd19_0_4 : subd19_0 [-2, 0] = true := by decide +kernel
theorem subd19_0_5 : subd19_0 [-2, 1] = true := by decide +kernel
theorem subd19_0_6 : subd19_0 [-2, 2] = true := by decide +kernel
theorem subd19_0_7 : subd19_0 [-2, 3] = true := by decide +kernel
theorem subd19_0_8 : subd19_0 [-1, -4] = true := by decide +kernel
theorem subd19_0_9 : subd19_0 [-1, -3] = true := by decide +kernel
theorem subd19_0_10 : subd19_0 [-1, -2] = true := by decide +kernel
theorem subd19_0_11 : subd19_0 [-1, -1] = true := by decide +kernel
theorem subd19_0_12 : subd19_0 [-1, 0] = true := by decide +kernel
theorem subd19_0_13 : subd19_0 [-1, 1] = true := by decide +kernel
theorem subd19_0_14 : subd19_0 [-1, 2] = true := by decide +kernel
theorem subd19_0_15 : subd19_0 [-1, 3] = true := by decide +kernel
theorem subd19_0_16 : subd19_0 [0, -4] = true := by decide +kernel
theorem subd19_0_17 : subd19_0 [0, -3] = true := by decide +kernel
theorem subd19_0_18 : subd19_0 [0, -2] = true := by decide +kernel
theorem subd19_0_19 : subd19_0 [0, -1] = true := by decide +kernel
theorem subd19_0_20 : subd19_0 [0, 0] = true := by decide +kernel
theorem subd19_0_21 : subd19_0 [0, 1] = true := by decide +kernel
theorem subd19_0_22 : subd19_0 [0, 2] = true := by decide +kernel
theorem subd19_0_23 : subd19_0 [0, 3] = true := by decide +kernel
theorem subd19_0_24 : subd19_0 [1, -4] = true := by decide +kernel
theorem subd19_0_25 : subd19_0 [1, -3] = true := by decide +kernel
theorem subd19_0_26 : subd19_0 [1, -2] = true := by decide +kernel
theorem subd19_0_27 : subd19_0 [1, -1] = true := by decide +kernel
theorem subd19_0_28 : subd19_0 [1, 0] = true := by decide +kernel
theorem subd19_0_29 : subd19_0 [1, 1] = true := by decide +kernel
theorem subd19_0_30 : subd19_0 [1, 2] = true := by decide +kernel
theorem subd19_0_31 : subd19_0 [1, 3] = true := by decide +kernel
theorem sbd19_0_0 : ∀ q ∈ blkd19_0_0, subd19_0 q = true := by
  unfold blkd19_0_0
  exact List.forall_mem_cons.2 ⟨subd19_0_0, List.forall_mem_cons.2 ⟨subd19_0_1, List.forall_mem_cons.2 ⟨subd19_0_2, List.forall_mem_cons.2 ⟨subd19_0_3, List.forall_mem_cons.2 ⟨subd19_0_4, List.forall_mem_cons.2 ⟨subd19_0_5, List.forall_mem_cons.2 ⟨subd19_0_6, List.forall_mem_cons.2 ⟨subd19_0_7, List.forall_mem_cons.2 ⟨subd19_0_8, List.forall_mem_cons.2 ⟨subd19_0_9, List.forall_mem_cons.2 ⟨subd19_0_10, List.forall_mem_cons.2 ⟨subd19_0_11, List.forall_mem_cons.2 ⟨subd19_0_12, List.forall_mem_cons.2 ⟨subd19_0_13, List.forall_mem_cons.2 ⟨subd19_0_14, List.forall_mem_cons.2 ⟨subd19_0_15, List.forall_mem_cons.2 ⟨subd19_0_16, List.forall_mem_cons.2 ⟨subd19_0_17, List.forall_mem_cons.2 ⟨subd19_0_18, List.forall_mem_cons.2 ⟨subd19_0_19, List.forall_mem_cons.2 ⟨subd19_0_20, List.forall_mem_cons.2 ⟨subd19_0_21, List.forall_mem_cons.2 ⟨subd19_0_22, List.forall_mem_cons.2 ⟨subd19_0_23, List.forall_mem_cons.2 ⟨subd19_0_24, List.forall_mem_cons.2 ⟨subd19_0_25, List.forall_mem_cons.2 ⟨subd19_0_26, List.forall_mem_cons.2 ⟨subd19_0_27, List.forall_mem_cons.2 ⟨subd19_0_28, List.forall_mem_cons.2 ⟨subd19_0_29, List.forall_mem_cons.2 ⟨subd19_0_30, List.forall_mem_cons.2 ⟨subd19_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_32 : subd19_0 [2, -4] = true := by decide +kernel
theorem subd19_0_33 : subd19_0 [2, -3] = true := by decide +kernel
theorem subd19_0_34 : subd19_0 [2, -2] = true := by decide +kernel
theorem subd19_0_35 : subd19_0 [2, -1] = true := by decide +kernel
theorem subd19_0_36 : subd19_0 [2, 0] = true := by decide +kernel
theorem subd19_0_37 : subd19_0 [2, 1] = true := by decide +kernel
theorem subd19_0_38 : subd19_0 [2, 2] = true := by decide +kernel
theorem subd19_0_39 : subd19_0 [3] = true := by decide +kernel
theorem sbd19_0_1 : ∀ q ∈ blkd19_0_1, subd19_0 q = true := by
  unfold blkd19_0_1
  exact List.forall_mem_cons.2 ⟨subd19_0_32, List.forall_mem_cons.2 ⟨subd19_0_33, List.forall_mem_cons.2 ⟨subd19_0_34, List.forall_mem_cons.2 ⟨subd19_0_35, List.forall_mem_cons.2 ⟨subd19_0_36, List.forall_mem_cons.2 ⟨subd19_0_37, List.forall_mem_cons.2 ⟨subd19_0_38, List.forall_mem_cons.2 ⟨subd19_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_1 : ldCheck G d19_1.U d19_1.ms ldd19_1 = true := by decide +kernel
theorem pre_okd19_1 : subPre G cell19 d19_1 = true := by decide +kernel
theorem subd19_1_0 : subd19_1 [-1] = true := by decide +kernel
theorem subd19_1_1 : subd19_1 [0] = true := by decide +kernel
theorem subd19_1_2 : subd19_1 [1] = true := by decide +kernel
theorem sbd19_1_0 : ∀ q ∈ blkd19_1_0, subd19_1 q = true := by
  unfold blkd19_1_0
  exact List.forall_mem_cons.2 ⟨subd19_1_0, List.forall_mem_cons.2 ⟨subd19_1_1, List.forall_mem_cons.2 ⟨subd19_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd20_0 : ldCheck G d20_0.U d20_0.ms ldd20_0 = true := by decide +kernel
theorem pre_okd20_0 : subPre G cell20 d20_0 = true := by decide +kernel
theorem subd20_0_0 : subd20_0 [-2] = true := by decide +kernel
theorem subd20_0_1 : subd20_0 [-1] = true := by decide +kernel
theorem subd20_0_2 : subd20_0 [0] = true := by decide +kernel
theorem subd20_0_3 : subd20_0 [1] = true := by decide +kernel
theorem subd20_0_4 : subd20_0 [2] = true := by decide +kernel
theorem sbd20_0_0 : ∀ q ∈ blkd20_0_0, subd20_0 q = true := by
  unfold blkd20_0_0
  exact List.forall_mem_cons.2 ⟨subd20_0_0, List.forall_mem_cons.2 ⟨subd20_0_1, List.forall_mem_cons.2 ⟨subd20_0_2, List.forall_mem_cons.2 ⟨subd20_0_3, List.forall_mem_cons.2 ⟨subd20_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd20_1 : ldCheck G d20_1.U d20_1.ms ldd20_1 = true := by decide +kernel
theorem pre_okd20_1 : subPre G cell20 d20_1 = true := by decide +kernel
theorem subd20_1_0 : subd20_1 [] = true := by decide +kernel
theorem sbd20_1_0 : ∀ q ∈ blkd20_1_0, subd20_1 q = true := by
  unfold blkd20_1_0
  exact List.forall_mem_cons.2 ⟨subd20_1_0, List.forall_mem_nil _⟩
theorem ld_okd21_0 : ldCheck G d21_0.U d21_0.ms ldd21_0 = true := by decide +kernel
theorem pre_okd21_0 : subPre G cell21 d21_0 = true := by decide +kernel
theorem subd21_0_0 : subd21_0 [-2] = true := by decide +kernel
theorem subd21_0_1 : subd21_0 [-1] = true := by decide +kernel
theorem subd21_0_2 : subd21_0 [0] = true := by decide +kernel
theorem subd21_0_3 : subd21_0 [1] = true := by decide +kernel
theorem subd21_0_4 : subd21_0 [2] = true := by decide +kernel
theorem sbd21_0_0 : ∀ q ∈ blkd21_0_0, subd21_0 q = true := by
  unfold blkd21_0_0
  exact List.forall_mem_cons.2 ⟨subd21_0_0, List.forall_mem_cons.2 ⟨subd21_0_1, List.forall_mem_cons.2 ⟨subd21_0_2, List.forall_mem_cons.2 ⟨subd21_0_3, List.forall_mem_cons.2 ⟨subd21_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
