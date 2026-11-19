import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_7 : ldCheck G d12_7.U d12_7.ms ldd12_7 = true := by decide +kernel
theorem pre_okd12_7 : subPre G cell12 d12_7 = true := by decide +kernel
theorem subd12_7_0 : subd12_7 [-2] = true := by decide +kernel
theorem subd12_7_1 : subd12_7 [-1] = true := by decide +kernel
theorem subd12_7_2 : subd12_7 [0] = true := by decide +kernel
theorem subd12_7_3 : subd12_7 [1] = true := by decide +kernel
theorem subd12_7_4 : subd12_7 [2] = true := by decide +kernel
theorem sbd12_7_0 : ∀ q ∈ blkd12_7_0, subd12_7 q = true := by
  unfold blkd12_7_0
  exact List.forall_mem_cons.2 ⟨subd12_7_0, List.forall_mem_cons.2 ⟨subd12_7_1, List.forall_mem_cons.2 ⟨subd12_7_2, List.forall_mem_cons.2 ⟨subd12_7_3, List.forall_mem_cons.2 ⟨subd12_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_nil _⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-3] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-2] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-1] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [0] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [1] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [2] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [3] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-3] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [-2] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [-1] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [0] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [1] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [2] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [3] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-2] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-1] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [0] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [1] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [2] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [-2] = true := by decide +kernel
theorem subd13_4_1 : subd13_4 [-1] = true := by decide +kernel
theorem subd13_4_2 : subd13_4 [0] = true := by decide +kernel
theorem subd13_4_3 : subd13_4 [1] = true := by decide +kernel
theorem subd13_4_4 : subd13_4 [2] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_cons.2 ⟨subd13_4_1, List.forall_mem_cons.2 ⟨subd13_4_2, List.forall_mem_cons.2 ⟨subd13_4_3, List.forall_mem_cons.2 ⟨subd13_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_5 : ldCheck G d13_5.U d13_5.ms ldd13_5 = true := by decide +kernel
theorem pre_okd13_5 : subPre G cell13 d13_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
