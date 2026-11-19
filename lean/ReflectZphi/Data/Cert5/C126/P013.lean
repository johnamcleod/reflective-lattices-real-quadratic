import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-1] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [0] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [1] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_nil _⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_nil _⟩
theorem ld_okd12_5 : ldCheck G d12_5.U d12_5.ms ldd12_5 = true := by decide +kernel
theorem pre_okd12_5 : subPre G cell12 d12_5 = true := by decide +kernel
theorem subd12_5_0 : subd12_5 [-2] = true := by decide +kernel
theorem subd12_5_1 : subd12_5 [-1] = true := by decide +kernel
theorem subd12_5_2 : subd12_5 [0] = true := by decide +kernel
theorem subd12_5_3 : subd12_5 [1] = true := by decide +kernel
theorem subd12_5_4 : subd12_5 [2] = true := by decide +kernel
theorem sbd12_5_0 : ∀ q ∈ blkd12_5_0, subd12_5 q = true := by
  unfold blkd12_5_0
  exact List.forall_mem_cons.2 ⟨subd12_5_0, List.forall_mem_cons.2 ⟨subd12_5_1, List.forall_mem_cons.2 ⟨subd12_5_2, List.forall_mem_cons.2 ⟨subd12_5_3, List.forall_mem_cons.2 ⟨subd12_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_6 : ldCheck G d12_6.U d12_6.ms ldd12_6 = true := by decide +kernel
theorem pre_okd12_6 : subPre G cell12 d12_6 = true := by decide +kernel
theorem subd12_6_0 : subd12_6 [] = true := by decide +kernel
theorem sbd12_6_0 : ∀ q ∈ blkd12_6_0, subd12_6 q = true := by
  unfold blkd12_6_0
  exact List.forall_mem_cons.2 ⟨subd12_6_0, List.forall_mem_nil _⟩
theorem ld_okd12_7 : ldCheck G d12_7.U d12_7.ms ldd12_7 = true := by decide +kernel
theorem pre_okd12_7 : subPre G cell12 d12_7 = true := by decide +kernel
theorem subd12_7_0 : subd12_7 [] = true := by decide +kernel
theorem sbd12_7_0 : ∀ q ∈ blkd12_7_0, subd12_7 q = true := by
  unfold blkd12_7_0
  exact List.forall_mem_cons.2 ⟨subd12_7_0, List.forall_mem_nil _⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_nil _⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C126
