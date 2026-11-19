import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [-2] = true := by decide +kernel
theorem subd2_6_1 : subd2_6 [-1] = true := by decide +kernel
theorem subd2_6_2 : subd2_6 [0] = true := by decide +kernel
theorem subd2_6_3 : subd2_6 [1] = true := by decide +kernel
theorem subd2_6_4 : subd2_6 [2] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_cons.2 ⟨subd2_6_1, List.forall_mem_cons.2 ⟨subd2_6_2, List.forall_mem_cons.2 ⟨subd2_6_3, List.forall_mem_cons.2 ⟨subd2_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel
theorem subd2_7_0 : subd2_7 [-1] = true := by decide +kernel
theorem subd2_7_1 : subd2_7 [0] = true := by decide +kernel
theorem subd2_7_2 : subd2_7 [1] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_cons.2 ⟨subd2_7_1, List.forall_mem_cons.2 ⟨subd2_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd2_8 : ldCheck G d2_8.U d2_8.ms ldd2_8 = true := by decide +kernel
theorem pre_okd2_8 : subPre G cell2 d2_8 = true := by decide +kernel
theorem subd2_8_0 : subd2_8 [-2] = true := by decide +kernel
theorem subd2_8_1 : subd2_8 [-1] = true := by decide +kernel
theorem subd2_8_2 : subd2_8 [0] = true := by decide +kernel
theorem subd2_8_3 : subd2_8 [1] = true := by decide +kernel
theorem subd2_8_4 : subd2_8 [2] = true := by decide +kernel
theorem sbd2_8_0 : ∀ q ∈ blkd2_8_0, subd2_8 q = true := by
  unfold blkd2_8_0
  exact List.forall_mem_cons.2 ⟨subd2_8_0, List.forall_mem_cons.2 ⟨subd2_8_1, List.forall_mem_cons.2 ⟨subd2_8_2, List.forall_mem_cons.2 ⟨subd2_8_3, List.forall_mem_cons.2 ⟨subd2_8_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_9 : ldCheck G d2_9.U d2_9.ms ldd2_9 = true := by decide +kernel
theorem pre_okd2_9 : subPre G cell2 d2_9 = true := by decide +kernel
theorem subd2_9_0 : subd2_9 [] = true := by decide +kernel
theorem sbd2_9_0 : ∀ q ∈ blkd2_9_0, subd2_9 q = true := by
  unfold blkd2_9_0
  exact List.forall_mem_cons.2 ⟨subd2_9_0, List.forall_mem_nil _⟩
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

end ReflectZphi.Data.Cert5.C113
