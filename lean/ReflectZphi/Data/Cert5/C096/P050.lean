import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_1_0 : subd13_1 [-3] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-2] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-1, -3] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-1, -2] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-1, -1] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-1, 0] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [-1, 1] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [-1, 2] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [-1, 3] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [0, -4] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [0, -3] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [0, -2] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [0, -1] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [0, 0] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [0, 1] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [0, 2] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [0, 3] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [1, -4] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [1, -3] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [1, -2] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [1, -1] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [1, 0] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [1, 1] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [1, 2] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [2] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [3] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-3] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-2, -3] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-2, -2] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [-2, -1] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [-2, 0] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [-2, 1] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [-2, 2] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [-1, -4] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [-1, -3] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [-1, -2] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [-1, -1] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [-1, 0] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [-1, 1] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [-1, 2] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [-1, 3] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [0, -4] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [0, -3] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_18 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_19 : subd13_2 [0, 0] = true := by decide +kernel
theorem subd13_2_20 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_21 : subd13_2 [0, 2] = true := by decide +kernel
theorem subd13_2_22 : subd13_2 [0, 3] = true := by decide +kernel
theorem subd13_2_23 : subd13_2 [1, -4] = true := by decide +kernel
theorem subd13_2_24 : subd13_2 [1, -3] = true := by decide +kernel
theorem subd13_2_25 : subd13_2 [1, -2] = true := by decide +kernel
theorem subd13_2_26 : subd13_2 [1, -1] = true := by decide +kernel
theorem subd13_2_27 : subd13_2 [1, 0] = true := by decide +kernel
theorem subd13_2_28 : subd13_2 [1, 1] = true := by decide +kernel
theorem subd13_2_29 : subd13_2 [1, 2] = true := by decide +kernel
theorem subd13_2_30 : subd13_2 [1, 3] = true := by decide +kernel
theorem subd13_2_31 : subd13_2 [2, -3] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_cons.2 ⟨subd13_2_18, List.forall_mem_cons.2 ⟨subd13_2_19, List.forall_mem_cons.2 ⟨subd13_2_20, List.forall_mem_cons.2 ⟨subd13_2_21, List.forall_mem_cons.2 ⟨subd13_2_22, List.forall_mem_cons.2 ⟨subd13_2_23, List.forall_mem_cons.2 ⟨subd13_2_24, List.forall_mem_cons.2 ⟨subd13_2_25, List.forall_mem_cons.2 ⟨subd13_2_26, List.forall_mem_cons.2 ⟨subd13_2_27, List.forall_mem_cons.2 ⟨subd13_2_28, List.forall_mem_cons.2 ⟨subd13_2_29, List.forall_mem_cons.2 ⟨subd13_2_30, List.forall_mem_cons.2 ⟨subd13_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_32 : subd13_2 [2, -2] = true := by decide +kernel
theorem subd13_2_33 : subd13_2 [2, -1] = true := by decide +kernel
theorem subd13_2_34 : subd13_2 [2, 0] = true := by decide +kernel
theorem subd13_2_35 : subd13_2 [2, 1] = true := by decide +kernel
theorem subd13_2_36 : subd13_2 [2, 2] = true := by decide +kernel
theorem subd13_2_37 : subd13_2 [3] = true := by decide +kernel
theorem sbd13_2_1 : ∀ q ∈ blkd13_2_1, subd13_2 q = true := by
  unfold blkd13_2_1
  exact List.forall_mem_cons.2 ⟨subd13_2_32, List.forall_mem_cons.2 ⟨subd13_2_33, List.forall_mem_cons.2 ⟨subd13_2_34, List.forall_mem_cons.2 ⟨subd13_2_35, List.forall_mem_cons.2 ⟨subd13_2_36, List.forall_mem_cons.2 ⟨subd13_2_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2, -4] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-2, -3] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-2, -2] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-2, -1] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-2, 0] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-2, 1] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [-2, 2] = true := by decide +kernel
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
theorem subd13_3_32 : subd13_3 [2, -3] = true := by decide +kernel
theorem subd13_3_33 : subd13_3 [2, -2] = true := by decide +kernel
theorem subd13_3_34 : subd13_3 [2, -1] = true := by decide +kernel
theorem subd13_3_35 : subd13_3 [2, 0] = true := by decide +kernel
theorem subd13_3_36 : subd13_3 [2, 1] = true := by decide +kernel
theorem subd13_3_37 : subd13_3 [2, 2] = true := by decide +kernel
theorem subd13_3_38 : subd13_3 [2, 3] = true := by decide +kernel
theorem subd13_3_39 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_1 : ∀ q ∈ blkd13_3_1, subd13_3 q = true := by
  unfold blkd13_3_1
  exact List.forall_mem_cons.2 ⟨subd13_3_32, List.forall_mem_cons.2 ⟨subd13_3_33, List.forall_mem_cons.2 ⟨subd13_3_34, List.forall_mem_cons.2 ⟨subd13_3_35, List.forall_mem_cons.2 ⟨subd13_3_36, List.forall_mem_cons.2 ⟨subd13_3_37, List.forall_mem_cons.2 ⟨subd13_3_38, List.forall_mem_cons.2 ⟨subd13_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [-1] = true := by decide +kernel
theorem subd13_4_1 : subd13_4 [0, -2] = true := by decide +kernel
theorem subd13_4_2 : subd13_4 [0, -1] = true := by decide +kernel
theorem subd13_4_3 : subd13_4 [0, 0] = true := by decide +kernel
theorem subd13_4_4 : subd13_4 [0, 1] = true := by decide +kernel
theorem subd13_4_5 : subd13_4 [1] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_cons.2 ⟨subd13_4_1, List.forall_mem_cons.2 ⟨subd13_4_2, List.forall_mem_cons.2 ⟨subd13_4_3, List.forall_mem_cons.2 ⟨subd13_4_4, List.forall_mem_cons.2 ⟨subd13_4_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
