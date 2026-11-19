import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-2] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-1] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [0] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [1] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [2] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-2] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-1] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [0] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [1] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [2] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2, -3] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-2, -2] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-2, -1] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-2, 0] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-2, 1] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-2, 2] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-2, 3] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [-1, -4] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [-1, -2] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [-1, -1] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [-1, 0] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [-1, 1] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [-1, 2] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [-1, 3] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [0, -4] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [0, -2] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [0, -1] = true := by decide +kernel
theorem subd13_3_20 : subd13_3 [0, 0] = true := by decide +kernel
theorem subd13_3_21 : subd13_3 [0, 1] = true := by decide +kernel
theorem subd13_3_22 : subd13_3 [0, 2] = true := by decide +kernel
theorem subd13_3_23 : subd13_3 [0, 3] = true := by decide +kernel
theorem subd13_3_24 : subd13_3 [1, -4] = true := by decide +kernel
theorem subd13_3_25 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_26 : subd13_3 [1, -2] = true := by decide +kernel
theorem subd13_3_27 : subd13_3 [1, -1] = true := by decide +kernel
theorem subd13_3_28 : subd13_3 [1, 0] = true := by decide +kernel
theorem subd13_3_29 : subd13_3 [1, 1] = true := by decide +kernel
theorem subd13_3_30 : subd13_3 [1, 2] = true := by decide +kernel
theorem subd13_3_31 : subd13_3 [1, 3] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_cons.2 ⟨subd13_3_20, List.forall_mem_cons.2 ⟨subd13_3_21, List.forall_mem_cons.2 ⟨subd13_3_22, List.forall_mem_cons.2 ⟨subd13_3_23, List.forall_mem_cons.2 ⟨subd13_3_24, List.forall_mem_cons.2 ⟨subd13_3_25, List.forall_mem_cons.2 ⟨subd13_3_26, List.forall_mem_cons.2 ⟨subd13_3_27, List.forall_mem_cons.2 ⟨subd13_3_28, List.forall_mem_cons.2 ⟨subd13_3_29, List.forall_mem_cons.2 ⟨subd13_3_30, List.forall_mem_cons.2 ⟨subd13_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_32 : subd13_3 [2, -4] = true := by decide +kernel
theorem subd13_3_33 : subd13_3 [2, -3] = true := by decide +kernel
theorem subd13_3_34 : subd13_3 [2, -2] = true := by decide +kernel
theorem subd13_3_35 : subd13_3 [2, -1] = true := by decide +kernel
theorem subd13_3_36 : subd13_3 [2, 0] = true := by decide +kernel
theorem subd13_3_37 : subd13_3 [2, 1] = true := by decide +kernel
theorem subd13_3_38 : subd13_3 [2, 2] = true := by decide +kernel
theorem subd13_3_39 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_1 : ∀ q ∈ blkd13_3_1, subd13_3 q = true := by
  unfold blkd13_3_1
  exact List.forall_mem_cons.2 ⟨subd13_3_32, List.forall_mem_cons.2 ⟨subd13_3_33, List.forall_mem_cons.2 ⟨subd13_3_34, List.forall_mem_cons.2 ⟨subd13_3_35, List.forall_mem_cons.2 ⟨subd13_3_36, List.forall_mem_cons.2 ⟨subd13_3_37, List.forall_mem_cons.2 ⟨subd13_3_38, List.forall_mem_cons.2 ⟨subd13_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_nil _⟩
theorem ld_okd13_5 : ldCheck G d13_5.U d13_5.ms ldd13_5 = true := by decide +kernel
theorem pre_okd13_5 : subPre G cell13 d13_5 = true := by decide +kernel
theorem subd13_5_0 : subd13_5 [] = true := by decide +kernel
theorem sbd13_5_0 : ∀ q ∈ blkd13_5_0, subd13_5 q = true := by
  unfold blkd13_5_0
  exact List.forall_mem_cons.2 ⟨subd13_5_0, List.forall_mem_nil _⟩
theorem ld_okd13_6 : ldCheck G d13_6.U d13_6.ms ldd13_6 = true := by decide +kernel
theorem pre_okd13_6 : subPre G cell13 d13_6 = true := by decide +kernel
theorem subd13_6_0 : subd13_6 [-2] = true := by decide +kernel
theorem subd13_6_1 : subd13_6 [-1] = true := by decide +kernel
theorem subd13_6_2 : subd13_6 [0, -3] = true := by decide +kernel
theorem subd13_6_3 : subd13_6 [0, -2] = true := by decide +kernel
theorem subd13_6_4 : subd13_6 [0, -1] = true := by decide +kernel
theorem subd13_6_5 : subd13_6 [0, 0] = true := by decide +kernel
theorem subd13_6_6 : subd13_6 [0, 1] = true := by decide +kernel
theorem subd13_6_7 : subd13_6 [0, 2] = true := by decide +kernel
theorem subd13_6_8 : subd13_6 [1] = true := by decide +kernel
theorem subd13_6_9 : subd13_6 [2] = true := by decide +kernel
theorem sbd13_6_0 : ∀ q ∈ blkd13_6_0, subd13_6 q = true := by
  unfold blkd13_6_0
  exact List.forall_mem_cons.2 ⟨subd13_6_0, List.forall_mem_cons.2 ⟨subd13_6_1, List.forall_mem_cons.2 ⟨subd13_6_2, List.forall_mem_cons.2 ⟨subd13_6_3, List.forall_mem_cons.2 ⟨subd13_6_4, List.forall_mem_cons.2 ⟨subd13_6_5, List.forall_mem_cons.2 ⟨subd13_6_6, List.forall_mem_cons.2 ⟨subd13_6_7, List.forall_mem_cons.2 ⟨subd13_6_8, List.forall_mem_cons.2 ⟨subd13_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
