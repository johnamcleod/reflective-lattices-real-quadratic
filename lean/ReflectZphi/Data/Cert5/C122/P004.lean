import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_4_0 : subd3_4 [-2, -2] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-2, -1] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-2, 0] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-2, 1] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-2, 2] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-1, -3] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-1, -1] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-1, 0] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [-1, 1] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [-1, 2] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [0, -3] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [0, -1] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [0, 0] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [0, 1] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [0, 2] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [1, -3] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [1, -1] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [1, 0] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [1, 1] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [1, 2] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [2, -3] = true := by decide +kernel
theorem subd3_4_24 : subd3_4 [2, -2] = true := by decide +kernel
theorem subd3_4_25 : subd3_4 [2, -1] = true := by decide +kernel
theorem subd3_4_26 : subd3_4 [2, 0] = true := by decide +kernel
theorem subd3_4_27 : subd3_4 [2, 1] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_cons.2 ⟨subd3_4_24, List.forall_mem_cons.2 ⟨subd3_4_25, List.forall_mem_cons.2 ⟨subd3_4_26, List.forall_mem_cons.2 ⟨subd3_4_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-2] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [-1] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [0] = true := by decide +kernel
theorem subd3_5_3 : subd3_5 [1] = true := by decide +kernel
theorem subd3_5_4 : subd3_5 [2] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_cons.2 ⟨subd3_5_3, List.forall_mem_cons.2 ⟨subd3_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel
theorem subd3_6_0 : subd3_6 [] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_nil _⟩
theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_nil _⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [1] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-2] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-1] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [0] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [2] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
