import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [-3] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [-2] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [-1, -4] = true := by decide +kernel
theorem subd2_3_3 : subd2_3 [-1, -3] = true := by decide +kernel
theorem subd2_3_4 : subd2_3 [-1, -2] = true := by decide +kernel
theorem subd2_3_5 : subd2_3 [-1, -1] = true := by decide +kernel
theorem subd2_3_6 : subd2_3 [-1, 0] = true := by decide +kernel
theorem subd2_3_7 : subd2_3 [-1, 1] = true := by decide +kernel
theorem subd2_3_8 : subd2_3 [-1, 2] = true := by decide +kernel
theorem subd2_3_9 : subd2_3 [0, -4] = true := by decide +kernel
theorem subd2_3_10 : subd2_3 [0, -3] = true := by decide +kernel
theorem subd2_3_11 : subd2_3 [0, -2] = true := by decide +kernel
theorem subd2_3_12 : subd2_3 [0, -1] = true := by decide +kernel
theorem subd2_3_13 : subd2_3 [0, 0] = true := by decide +kernel
theorem subd2_3_14 : subd2_3 [0, 1] = true := by decide +kernel
theorem subd2_3_15 : subd2_3 [0, 2] = true := by decide +kernel
theorem subd2_3_16 : subd2_3 [0, 3] = true := by decide +kernel
theorem subd2_3_17 : subd2_3 [1, -3] = true := by decide +kernel
theorem subd2_3_18 : subd2_3 [1, -2] = true := by decide +kernel
theorem subd2_3_19 : subd2_3 [1, -1] = true := by decide +kernel
theorem subd2_3_20 : subd2_3 [1, 0] = true := by decide +kernel
theorem subd2_3_21 : subd2_3 [1, 1] = true := by decide +kernel
theorem subd2_3_22 : subd2_3 [1, 2] = true := by decide +kernel
theorem subd2_3_23 : subd2_3 [1, 3] = true := by decide +kernel
theorem subd2_3_24 : subd2_3 [2] = true := by decide +kernel
theorem subd2_3_25 : subd2_3 [3] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_cons.2 ⟨subd2_3_3, List.forall_mem_cons.2 ⟨subd2_3_4, List.forall_mem_cons.2 ⟨subd2_3_5, List.forall_mem_cons.2 ⟨subd2_3_6, List.forall_mem_cons.2 ⟨subd2_3_7, List.forall_mem_cons.2 ⟨subd2_3_8, List.forall_mem_cons.2 ⟨subd2_3_9, List.forall_mem_cons.2 ⟨subd2_3_10, List.forall_mem_cons.2 ⟨subd2_3_11, List.forall_mem_cons.2 ⟨subd2_3_12, List.forall_mem_cons.2 ⟨subd2_3_13, List.forall_mem_cons.2 ⟨subd2_3_14, List.forall_mem_cons.2 ⟨subd2_3_15, List.forall_mem_cons.2 ⟨subd2_3_16, List.forall_mem_cons.2 ⟨subd2_3_17, List.forall_mem_cons.2 ⟨subd2_3_18, List.forall_mem_cons.2 ⟨subd2_3_19, List.forall_mem_cons.2 ⟨subd2_3_20, List.forall_mem_cons.2 ⟨subd2_3_21, List.forall_mem_cons.2 ⟨subd2_3_22, List.forall_mem_cons.2 ⟨subd2_3_23, List.forall_mem_cons.2 ⟨subd2_3_24, List.forall_mem_cons.2 ⟨subd2_3_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [-2] = true := by decide +kernel
theorem subd2_4_1 : subd2_4 [-1] = true := by decide +kernel
theorem subd2_4_2 : subd2_4 [0] = true := by decide +kernel
theorem subd2_4_3 : subd2_4 [1] = true := by decide +kernel
theorem subd2_4_4 : subd2_4 [2] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_cons.2 ⟨subd2_4_1, List.forall_mem_cons.2 ⟨subd2_4_2, List.forall_mem_cons.2 ⟨subd2_4_3, List.forall_mem_cons.2 ⟨subd2_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
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
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C140
