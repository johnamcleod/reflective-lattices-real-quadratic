import ReflectZphi.Data.Cert5.C112.Base

namespace ReflectZphi.Data.Cert5.C112

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [-3] = true := by decide +kernel
theorem subd2_2_1 : subd2_2 [-2, -3] = true := by decide +kernel
theorem subd2_2_2 : subd2_2 [-2, -2] = true := by decide +kernel
theorem subd2_2_3 : subd2_2 [-2, -1] = true := by decide +kernel
theorem subd2_2_4 : subd2_2 [-2, 0] = true := by decide +kernel
theorem subd2_2_5 : subd2_2 [-2, 1] = true := by decide +kernel
theorem subd2_2_6 : subd2_2 [-2, 2] = true := by decide +kernel
theorem subd2_2_7 : subd2_2 [-1, -4] = true := by decide +kernel
theorem subd2_2_8 : subd2_2 [-1, -3] = true := by decide +kernel
theorem subd2_2_9 : subd2_2 [-1, -2] = true := by decide +kernel
theorem subd2_2_10 : subd2_2 [-1, -1] = true := by decide +kernel
theorem subd2_2_11 : subd2_2 [-1, 0] = true := by decide +kernel
theorem subd2_2_12 : subd2_2 [-1, 1] = true := by decide +kernel
theorem subd2_2_13 : subd2_2 [-1, 2] = true := by decide +kernel
theorem subd2_2_14 : subd2_2 [0, -4] = true := by decide +kernel
theorem subd2_2_15 : subd2_2 [0, -3] = true := by decide +kernel
theorem subd2_2_16 : subd2_2 [0, -2] = true := by decide +kernel
theorem subd2_2_17 : subd2_2 [0, -1] = true := by decide +kernel
theorem subd2_2_18 : subd2_2 [0, 0] = true := by decide +kernel
theorem subd2_2_19 : subd2_2 [0, 1] = true := by decide +kernel
theorem subd2_2_20 : subd2_2 [0, 2] = true := by decide +kernel
theorem subd2_2_21 : subd2_2 [0, 3] = true := by decide +kernel
theorem subd2_2_22 : subd2_2 [1, -3] = true := by decide +kernel
theorem subd2_2_23 : subd2_2 [1, -2] = true := by decide +kernel
theorem subd2_2_24 : subd2_2 [1, -1] = true := by decide +kernel
theorem subd2_2_25 : subd2_2 [1, 0] = true := by decide +kernel
theorem subd2_2_26 : subd2_2 [1, 1] = true := by decide +kernel
theorem subd2_2_27 : subd2_2 [1, 2] = true := by decide +kernel
theorem subd2_2_28 : subd2_2 [1, 3] = true := by decide +kernel
theorem subd2_2_29 : subd2_2 [2, -3] = true := by decide +kernel
theorem subd2_2_30 : subd2_2 [2, -2] = true := by decide +kernel
theorem subd2_2_31 : subd2_2 [2, -1] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_cons.2 ⟨subd2_2_1, List.forall_mem_cons.2 ⟨subd2_2_2, List.forall_mem_cons.2 ⟨subd2_2_3, List.forall_mem_cons.2 ⟨subd2_2_4, List.forall_mem_cons.2 ⟨subd2_2_5, List.forall_mem_cons.2 ⟨subd2_2_6, List.forall_mem_cons.2 ⟨subd2_2_7, List.forall_mem_cons.2 ⟨subd2_2_8, List.forall_mem_cons.2 ⟨subd2_2_9, List.forall_mem_cons.2 ⟨subd2_2_10, List.forall_mem_cons.2 ⟨subd2_2_11, List.forall_mem_cons.2 ⟨subd2_2_12, List.forall_mem_cons.2 ⟨subd2_2_13, List.forall_mem_cons.2 ⟨subd2_2_14, List.forall_mem_cons.2 ⟨subd2_2_15, List.forall_mem_cons.2 ⟨subd2_2_16, List.forall_mem_cons.2 ⟨subd2_2_17, List.forall_mem_cons.2 ⟨subd2_2_18, List.forall_mem_cons.2 ⟨subd2_2_19, List.forall_mem_cons.2 ⟨subd2_2_20, List.forall_mem_cons.2 ⟨subd2_2_21, List.forall_mem_cons.2 ⟨subd2_2_22, List.forall_mem_cons.2 ⟨subd2_2_23, List.forall_mem_cons.2 ⟨subd2_2_24, List.forall_mem_cons.2 ⟨subd2_2_25, List.forall_mem_cons.2 ⟨subd2_2_26, List.forall_mem_cons.2 ⟨subd2_2_27, List.forall_mem_cons.2 ⟨subd2_2_28, List.forall_mem_cons.2 ⟨subd2_2_29, List.forall_mem_cons.2 ⟨subd2_2_30, List.forall_mem_cons.2 ⟨subd2_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_2_32 : subd2_2 [2, 0] = true := by decide +kernel
theorem subd2_2_33 : subd2_2 [2, 1] = true := by decide +kernel
theorem subd2_2_34 : subd2_2 [2, 2] = true := by decide +kernel
theorem subd2_2_35 : subd2_2 [3] = true := by decide +kernel
theorem sbd2_2_1 : ∀ q ∈ blkd2_2_1, subd2_2 q = true := by
  unfold blkd2_2_1
  exact List.forall_mem_cons.2 ⟨subd2_2_32, List.forall_mem_cons.2 ⟨subd2_2_33, List.forall_mem_cons.2 ⟨subd2_2_34, List.forall_mem_cons.2 ⟨subd2_2_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [-2] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [-1] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [0] = true := by decide +kernel
theorem subd2_3_3 : subd2_3 [1] = true := by decide +kernel
theorem subd2_3_4 : subd2_3 [2] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_cons.2 ⟨subd2_3_3, List.forall_mem_cons.2 ⟨subd2_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [-2] = true := by decide +kernel
theorem subd2_4_1 : subd2_4 [-1] = true := by decide +kernel
theorem subd2_4_2 : subd2_4 [0, -3] = true := by decide +kernel
theorem subd2_4_3 : subd2_4 [0, -2] = true := by decide +kernel
theorem subd2_4_4 : subd2_4 [0, -1] = true := by decide +kernel
theorem subd2_4_5 : subd2_4 [0, 0] = true := by decide +kernel
theorem subd2_4_6 : subd2_4 [0, 1] = true := by decide +kernel
theorem subd2_4_7 : subd2_4 [0, 2] = true := by decide +kernel
theorem subd2_4_8 : subd2_4 [1] = true := by decide +kernel
theorem subd2_4_9 : subd2_4 [2] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_cons.2 ⟨subd2_4_1, List.forall_mem_cons.2 ⟨subd2_4_2, List.forall_mem_cons.2 ⟨subd2_4_3, List.forall_mem_cons.2 ⟨subd2_4_4, List.forall_mem_cons.2 ⟨subd2_4_5, List.forall_mem_cons.2 ⟨subd2_4_6, List.forall_mem_cons.2 ⟨subd2_4_7, List.forall_mem_cons.2 ⟨subd2_4_8, List.forall_mem_cons.2 ⟨subd2_4_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_nil _⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C112
