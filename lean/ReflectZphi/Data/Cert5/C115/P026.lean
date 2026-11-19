import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd16_6 : ldCheck G d16_6.U d16_6.ms ldd16_6 = true := by decide +kernel
theorem pre_okd16_6 : subPre G cell16 d16_6 = true := by decide +kernel
theorem subd16_6_0 : subd16_6 [-2] = true := by decide +kernel
theorem subd16_6_1 : subd16_6 [-1, -3] = true := by decide +kernel
theorem subd16_6_2 : subd16_6 [-1, -2] = true := by decide +kernel
theorem subd16_6_3 : subd16_6 [-1, -1] = true := by decide +kernel
theorem subd16_6_4 : subd16_6 [-1, 0] = true := by decide +kernel
theorem subd16_6_5 : subd16_6 [-1, 1] = true := by decide +kernel
theorem subd16_6_6 : subd16_6 [0, -3] = true := by decide +kernel
theorem subd16_6_7 : subd16_6 [0, -2] = true := by decide +kernel
theorem subd16_6_8 : subd16_6 [0, -1] = true := by decide +kernel
theorem subd16_6_9 : subd16_6 [0, 0] = true := by decide +kernel
theorem subd16_6_10 : subd16_6 [0, 1] = true := by decide +kernel
theorem subd16_6_11 : subd16_6 [0, 2] = true := by decide +kernel
theorem subd16_6_12 : subd16_6 [1, -2] = true := by decide +kernel
theorem subd16_6_13 : subd16_6 [1, -1] = true := by decide +kernel
theorem subd16_6_14 : subd16_6 [1, 0] = true := by decide +kernel
theorem subd16_6_15 : subd16_6 [1, 1] = true := by decide +kernel
theorem subd16_6_16 : subd16_6 [1, 2] = true := by decide +kernel
theorem subd16_6_17 : subd16_6 [2] = true := by decide +kernel
theorem sbd16_6_0 : ∀ q ∈ blkd16_6_0, subd16_6 q = true := by
  unfold blkd16_6_0
  exact List.forall_mem_cons.2 ⟨subd16_6_0, List.forall_mem_cons.2 ⟨subd16_6_1, List.forall_mem_cons.2 ⟨subd16_6_2, List.forall_mem_cons.2 ⟨subd16_6_3, List.forall_mem_cons.2 ⟨subd16_6_4, List.forall_mem_cons.2 ⟨subd16_6_5, List.forall_mem_cons.2 ⟨subd16_6_6, List.forall_mem_cons.2 ⟨subd16_6_7, List.forall_mem_cons.2 ⟨subd16_6_8, List.forall_mem_cons.2 ⟨subd16_6_9, List.forall_mem_cons.2 ⟨subd16_6_10, List.forall_mem_cons.2 ⟨subd16_6_11, List.forall_mem_cons.2 ⟨subd16_6_12, List.forall_mem_cons.2 ⟨subd16_6_13, List.forall_mem_cons.2 ⟨subd16_6_14, List.forall_mem_cons.2 ⟨subd16_6_15, List.forall_mem_cons.2 ⟨subd16_6_16, List.forall_mem_cons.2 ⟨subd16_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_7 : ldCheck G d16_7.U d16_7.ms ldd16_7 = true := by decide +kernel
theorem pre_okd16_7 : subPre G cell16 d16_7 = true := by decide +kernel
theorem subd16_7_0 : subd16_7 [-1] = true := by decide +kernel
theorem subd16_7_1 : subd16_7 [0] = true := by decide +kernel
theorem subd16_7_2 : subd16_7 [1] = true := by decide +kernel
theorem sbd16_7_0 : ∀ q ∈ blkd16_7_0, subd16_7 q = true := by
  unfold blkd16_7_0
  exact List.forall_mem_cons.2 ⟨subd16_7_0, List.forall_mem_cons.2 ⟨subd16_7_1, List.forall_mem_cons.2 ⟨subd16_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd16_8 : ldCheck G d16_8.U d16_8.ms ldd16_8 = true := by decide +kernel
theorem pre_okd16_8 : subPre G cell16 d16_8 = true := by decide +kernel
theorem subd16_8_0 : subd16_8 [-2] = true := by decide +kernel
theorem subd16_8_1 : subd16_8 [-1, -3] = true := by decide +kernel
theorem subd16_8_2 : subd16_8 [-1, -2] = true := by decide +kernel
theorem subd16_8_3 : subd16_8 [-1, -1] = true := by decide +kernel
theorem subd16_8_4 : subd16_8 [-1, 0] = true := by decide +kernel
theorem subd16_8_5 : subd16_8 [-1, 1] = true := by decide +kernel
theorem subd16_8_6 : subd16_8 [-1, 2] = true := by decide +kernel
theorem subd16_8_7 : subd16_8 [0, -3] = true := by decide +kernel
theorem subd16_8_8 : subd16_8 [0, -2] = true := by decide +kernel
theorem subd16_8_9 : subd16_8 [0, -1] = true := by decide +kernel
theorem subd16_8_10 : subd16_8 [0, 0] = true := by decide +kernel
theorem subd16_8_11 : subd16_8 [0, 1] = true := by decide +kernel
theorem subd16_8_12 : subd16_8 [0, 2] = true := by decide +kernel
theorem subd16_8_13 : subd16_8 [1, -3] = true := by decide +kernel
theorem subd16_8_14 : subd16_8 [1, -2] = true := by decide +kernel
theorem subd16_8_15 : subd16_8 [1, -1] = true := by decide +kernel
theorem subd16_8_16 : subd16_8 [1, 0] = true := by decide +kernel
theorem subd16_8_17 : subd16_8 [1, 1] = true := by decide +kernel
theorem subd16_8_18 : subd16_8 [1, 2] = true := by decide +kernel
theorem subd16_8_19 : subd16_8 [2] = true := by decide +kernel
theorem sbd16_8_0 : ∀ q ∈ blkd16_8_0, subd16_8 q = true := by
  unfold blkd16_8_0
  exact List.forall_mem_cons.2 ⟨subd16_8_0, List.forall_mem_cons.2 ⟨subd16_8_1, List.forall_mem_cons.2 ⟨subd16_8_2, List.forall_mem_cons.2 ⟨subd16_8_3, List.forall_mem_cons.2 ⟨subd16_8_4, List.forall_mem_cons.2 ⟨subd16_8_5, List.forall_mem_cons.2 ⟨subd16_8_6, List.forall_mem_cons.2 ⟨subd16_8_7, List.forall_mem_cons.2 ⟨subd16_8_8, List.forall_mem_cons.2 ⟨subd16_8_9, List.forall_mem_cons.2 ⟨subd16_8_10, List.forall_mem_cons.2 ⟨subd16_8_11, List.forall_mem_cons.2 ⟨subd16_8_12, List.forall_mem_cons.2 ⟨subd16_8_13, List.forall_mem_cons.2 ⟨subd16_8_14, List.forall_mem_cons.2 ⟨subd16_8_15, List.forall_mem_cons.2 ⟨subd16_8_16, List.forall_mem_cons.2 ⟨subd16_8_17, List.forall_mem_cons.2 ⟨subd16_8_18, List.forall_mem_cons.2 ⟨subd16_8_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_9 : ldCheck G d16_9.U d16_9.ms ldd16_9 = true := by decide +kernel
theorem pre_okd16_9 : subPre G cell16 d16_9 = true := by decide +kernel
theorem subd16_9_0 : subd16_9 [] = true := by decide +kernel
theorem sbd16_9_0 : ∀ q ∈ blkd16_9_0, subd16_9 q = true := by
  unfold blkd16_9_0
  exact List.forall_mem_cons.2 ⟨subd16_9_0, List.forall_mem_nil _⟩
theorem ld_okd16_10 : ldCheck G d16_10.U d16_10.ms ldd16_10 = true := by decide +kernel
theorem pre_okd16_10 : subPre G cell16 d16_10 = true := by decide +kernel
theorem subd16_10_0 : subd16_10 [-2] = true := by decide +kernel
theorem subd16_10_1 : subd16_10 [-1] = true := by decide +kernel
theorem subd16_10_2 : subd16_10 [0] = true := by decide +kernel
theorem subd16_10_3 : subd16_10 [1] = true := by decide +kernel
theorem subd16_10_4 : subd16_10 [2] = true := by decide +kernel
theorem sbd16_10_0 : ∀ q ∈ blkd16_10_0, subd16_10 q = true := by
  unfold blkd16_10_0
  exact List.forall_mem_cons.2 ⟨subd16_10_0, List.forall_mem_cons.2 ⟨subd16_10_1, List.forall_mem_cons.2 ⟨subd16_10_2, List.forall_mem_cons.2 ⟨subd16_10_3, List.forall_mem_cons.2 ⟨subd16_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd16_11 : ldCheck G d16_11.U d16_11.ms ldd16_11 = true := by decide +kernel
theorem pre_okd16_11 : subPre G cell16 d16_11 = true := by decide +kernel
theorem subd16_11_0 : subd16_11 [] = true := by decide +kernel
theorem sbd16_11_0 : ∀ q ∈ blkd16_11_0, subd16_11 q = true := by
  unfold blkd16_11_0
  exact List.forall_mem_cons.2 ⟨subd16_11_0, List.forall_mem_nil _⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
