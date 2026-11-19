import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_7 : ldCheck G d3_7.U d3_7.ms ldd3_7 = true := by decide +kernel
theorem pre_okd3_7 : subPre G cell3 d3_7 = true := by decide +kernel
theorem subd3_7_0 : subd3_7 [-1] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [0] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [1] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-1] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [0] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [1] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-1] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [0] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [1] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [2] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-2] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [0, 0] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [1, -2] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [1, 1] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [2] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_nil _⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C132
