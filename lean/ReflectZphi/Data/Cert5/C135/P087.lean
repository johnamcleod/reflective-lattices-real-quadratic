import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd15_7 : ldCheck G d15_7.U d15_7.ms ldd15_7 = true := by decide +kernel
theorem pre_okd15_7 : subPre G cell15 d15_7 = true := by decide +kernel
theorem subd15_7_0 : subd15_7 [-2] = true := by decide +kernel
theorem subd15_7_1 : subd15_7 [-1] = true := by decide +kernel
theorem subd15_7_2 : subd15_7 [0] = true := by decide +kernel
theorem subd15_7_3 : subd15_7 [1] = true := by decide +kernel
theorem subd15_7_4 : subd15_7 [2] = true := by decide +kernel
theorem sbd15_7_0 : ∀ q ∈ blkd15_7_0, subd15_7 q = true := by
  unfold blkd15_7_0
  exact List.forall_mem_cons.2 ⟨subd15_7_0, List.forall_mem_cons.2 ⟨subd15_7_1, List.forall_mem_cons.2 ⟨subd15_7_2, List.forall_mem_cons.2 ⟨subd15_7_3, List.forall_mem_cons.2 ⟨subd15_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_nil _⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-2] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-1] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [0] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [2] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel
theorem subd16_2_0 : subd16_2 [-2] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [-1] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [0] = true := by decide +kernel
theorem subd16_2_3 : subd16_2 [1] = true := by decide +kernel
theorem subd16_2_4 : subd16_2 [2] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_cons.2 ⟨subd16_2_3, List.forall_mem_cons.2 ⟨subd16_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [-2] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [-1] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [0] = true := by decide +kernel
theorem subd16_3_3 : subd16_3 [1] = true := by decide +kernel
theorem subd16_3_4 : subd16_3 [2] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_cons.2 ⟨subd16_3_3, List.forall_mem_cons.2 ⟨subd16_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_4 : ldCheck G d16_4.U d16_4.ms ldd16_4 = true := by decide +kernel
theorem pre_okd16_4 : subPre G cell16 d16_4 = true := by decide +kernel
theorem subd16_4_0 : subd16_4 [-2] = true := by decide +kernel
theorem subd16_4_1 : subd16_4 [-1] = true := by decide +kernel
theorem subd16_4_2 : subd16_4 [0] = true := by decide +kernel
theorem subd16_4_3 : subd16_4 [1] = true := by decide +kernel
theorem subd16_4_4 : subd16_4 [2] = true := by decide +kernel
theorem sbd16_4_0 : ∀ q ∈ blkd16_4_0, subd16_4 q = true := by
  unfold blkd16_4_0
  exact List.forall_mem_cons.2 ⟨subd16_4_0, List.forall_mem_cons.2 ⟨subd16_4_1, List.forall_mem_cons.2 ⟨subd16_4_2, List.forall_mem_cons.2 ⟨subd16_4_3, List.forall_mem_cons.2 ⟨subd16_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_5 : ldCheck G d16_5.U d16_5.ms ldd16_5 = true := by decide +kernel
theorem pre_okd16_5 : subPre G cell16 d16_5 = true := by decide +kernel
theorem subd16_5_0 : subd16_5 [] = true := by decide +kernel
theorem sbd16_5_0 : ∀ q ∈ blkd16_5_0, subd16_5 q = true := by
  unfold blkd16_5_0
  exact List.forall_mem_cons.2 ⟨subd16_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C135
