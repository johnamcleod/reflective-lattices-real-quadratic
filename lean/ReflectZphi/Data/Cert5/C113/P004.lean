import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_nil _⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_nil _⟩
theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-1] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [0] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [1] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [-3] = true := by decide +kernel
theorem subd3_6_1 : subd3_6 [-2] = true := by decide +kernel
theorem subd3_6_2 : subd3_6 [-1, -3] = true := by decide +kernel
theorem subd3_6_3 : subd3_6 [-1, -2] = true := by decide +kernel
theorem subd3_6_4 : subd3_6 [-1, -1] = true := by decide +kernel
theorem subd3_6_5 : subd3_6 [-1, 0] = true := by decide +kernel
theorem subd3_6_6 : subd3_6 [-1, 1] = true := by decide +kernel
theorem subd3_6_7 : subd3_6 [-1, 2] = true := by decide +kernel
theorem subd3_6_8 : subd3_6 [0, -3] = true := by decide +kernel
theorem subd3_6_9 : subd3_6 [0, -2] = true := by decide +kernel
theorem subd3_6_10 : subd3_6 [0, -1] = true := by decide +kernel
theorem subd3_6_11 : subd3_6 [0, 0] = true := by decide +kernel
theorem subd3_6_12 : subd3_6 [0, 1] = true := by decide +kernel
theorem subd3_6_13 : subd3_6 [0, 2] = true := by decide +kernel
theorem subd3_6_14 : subd3_6 [1, -3] = true := by decide +kernel
theorem subd3_6_15 : subd3_6 [1, -2] = true := by decide +kernel
theorem subd3_6_16 : subd3_6 [1, -1] = true := by decide +kernel
theorem subd3_6_17 : subd3_6 [1, 0] = true := by decide +kernel
theorem subd3_6_18 : subd3_6 [1, 1] = true := by decide +kernel
theorem subd3_6_19 : subd3_6 [1, 2] = true := by decide +kernel
theorem subd3_6_20 : subd3_6 [2] = true := by decide +kernel
theorem subd3_6_21 : subd3_6 [3] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_cons.2 ⟨subd3_6_1, List.forall_mem_cons.2 ⟨subd3_6_2, List.forall_mem_cons.2 ⟨subd3_6_3, List.forall_mem_cons.2 ⟨subd3_6_4, List.forall_mem_cons.2 ⟨subd3_6_5, List.forall_mem_cons.2 ⟨subd3_6_6, List.forall_mem_cons.2 ⟨subd3_6_7, List.forall_mem_cons.2 ⟨subd3_6_8, List.forall_mem_cons.2 ⟨subd3_6_9, List.forall_mem_cons.2 ⟨subd3_6_10, List.forall_mem_cons.2 ⟨subd3_6_11, List.forall_mem_cons.2 ⟨subd3_6_12, List.forall_mem_cons.2 ⟨subd3_6_13, List.forall_mem_cons.2 ⟨subd3_6_14, List.forall_mem_cons.2 ⟨subd3_6_15, List.forall_mem_cons.2 ⟨subd3_6_16, List.forall_mem_cons.2 ⟨subd3_6_17, List.forall_mem_cons.2 ⟨subd3_6_18, List.forall_mem_cons.2 ⟨subd3_6_19, List.forall_mem_cons.2 ⟨subd3_6_20, List.forall_mem_cons.2 ⟨subd3_6_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-2] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-1, -4] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [-1, -3] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [-1, -2] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [-1, -1] = true := by decide +kernel
theorem subd3_7_5 : subd3_7 [-1, 0] = true := by decide +kernel
theorem subd3_7_6 : subd3_7 [-1, 1] = true := by decide +kernel
theorem subd3_7_7 : subd3_7 [-1, 2] = true := by decide +kernel
theorem subd3_7_8 : subd3_7 [0, -4] = true := by decide +kernel
theorem subd3_7_9 : subd3_7 [0, -3] = true := by decide +kernel
theorem subd3_7_10 : subd3_7 [0, -2] = true := by decide +kernel
theorem subd3_7_11 : subd3_7 [0, -1] = true := by decide +kernel
theorem subd3_7_12 : subd3_7 [0, 0] = true := by decide +kernel
theorem subd3_7_13 : subd3_7 [0, 1] = true := by decide +kernel
theorem subd3_7_14 : subd3_7 [0, 2] = true := by decide +kernel
theorem subd3_7_15 : subd3_7 [0, 3] = true := by decide +kernel
theorem subd3_7_16 : subd3_7 [1, -3] = true := by decide +kernel
theorem subd3_7_17 : subd3_7 [1, -2] = true := by decide +kernel
theorem subd3_7_18 : subd3_7 [1, -1] = true := by decide +kernel
theorem subd3_7_19 : subd3_7 [1, 0] = true := by decide +kernel
theorem subd3_7_20 : subd3_7 [1, 1] = true := by decide +kernel
theorem subd3_7_21 : subd3_7 [1, 2] = true := by decide +kernel
theorem subd3_7_22 : subd3_7 [1, 3] = true := by decide +kernel
theorem subd3_7_23 : subd3_7 [2] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_cons.2 ⟨subd3_7_5, List.forall_mem_cons.2 ⟨subd3_7_6, List.forall_mem_cons.2 ⟨subd3_7_7, List.forall_mem_cons.2 ⟨subd3_7_8, List.forall_mem_cons.2 ⟨subd3_7_9, List.forall_mem_cons.2 ⟨subd3_7_10, List.forall_mem_cons.2 ⟨subd3_7_11, List.forall_mem_cons.2 ⟨subd3_7_12, List.forall_mem_cons.2 ⟨subd3_7_13, List.forall_mem_cons.2 ⟨subd3_7_14, List.forall_mem_cons.2 ⟨subd3_7_15, List.forall_mem_cons.2 ⟨subd3_7_16, List.forall_mem_cons.2 ⟨subd3_7_17, List.forall_mem_cons.2 ⟨subd3_7_18, List.forall_mem_cons.2 ⟨subd3_7_19, List.forall_mem_cons.2 ⟨subd3_7_20, List.forall_mem_cons.2 ⟨subd3_7_21, List.forall_mem_cons.2 ⟨subd3_7_22, List.forall_mem_cons.2 ⟨subd3_7_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_8 : ldCheck G d3_8.U d3_8.ms ldd3_8 = true := by decide +kernel
theorem pre_okd3_8 : subPre G cell3 d3_8 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C113
