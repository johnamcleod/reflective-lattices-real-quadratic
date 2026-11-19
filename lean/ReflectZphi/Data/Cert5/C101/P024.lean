import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [-2] = true := by decide +kernel
theorem subd16_0_1 : subd16_0 [-1, -4] = true := by decide +kernel
theorem subd16_0_2 : subd16_0 [-1, -3] = true := by decide +kernel
theorem subd16_0_3 : subd16_0 [-1, -2] = true := by decide +kernel
theorem subd16_0_4 : subd16_0 [-1, -1] = true := by decide +kernel
theorem subd16_0_5 : subd16_0 [-1, 0] = true := by decide +kernel
theorem subd16_0_6 : subd16_0 [-1, 1] = true := by decide +kernel
theorem subd16_0_7 : subd16_0 [-1, 2] = true := by decide +kernel
theorem subd16_0_8 : subd16_0 [-1, 3] = true := by decide +kernel
theorem subd16_0_9 : subd16_0 [0, -4] = true := by decide +kernel
theorem subd16_0_10 : subd16_0 [0, -3] = true := by decide +kernel
theorem subd16_0_11 : subd16_0 [0, -2] = true := by decide +kernel
theorem subd16_0_12 : subd16_0 [0, -1] = true := by decide +kernel
theorem subd16_0_13 : subd16_0 [0, 0] = true := by decide +kernel
theorem subd16_0_14 : subd16_0 [0, 1] = true := by decide +kernel
theorem subd16_0_15 : subd16_0 [0, 2] = true := by decide +kernel
theorem subd16_0_16 : subd16_0 [0, 3] = true := by decide +kernel
theorem subd16_0_17 : subd16_0 [1, -4] = true := by decide +kernel
theorem subd16_0_18 : subd16_0 [1, -3] = true := by decide +kernel
theorem subd16_0_19 : subd16_0 [1, -2] = true := by decide +kernel
theorem subd16_0_20 : subd16_0 [1, -1] = true := by decide +kernel
theorem subd16_0_21 : subd16_0 [1, 0] = true := by decide +kernel
theorem subd16_0_22 : subd16_0 [1, 1] = true := by decide +kernel
theorem subd16_0_23 : subd16_0 [1, 2] = true := by decide +kernel
theorem subd16_0_24 : subd16_0 [1, 3] = true := by decide +kernel
theorem subd16_0_25 : subd16_0 [2] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_cons.2 ⟨subd16_0_1, List.forall_mem_cons.2 ⟨subd16_0_2, List.forall_mem_cons.2 ⟨subd16_0_3, List.forall_mem_cons.2 ⟨subd16_0_4, List.forall_mem_cons.2 ⟨subd16_0_5, List.forall_mem_cons.2 ⟨subd16_0_6, List.forall_mem_cons.2 ⟨subd16_0_7, List.forall_mem_cons.2 ⟨subd16_0_8, List.forall_mem_cons.2 ⟨subd16_0_9, List.forall_mem_cons.2 ⟨subd16_0_10, List.forall_mem_cons.2 ⟨subd16_0_11, List.forall_mem_cons.2 ⟨subd16_0_12, List.forall_mem_cons.2 ⟨subd16_0_13, List.forall_mem_cons.2 ⟨subd16_0_14, List.forall_mem_cons.2 ⟨subd16_0_15, List.forall_mem_cons.2 ⟨subd16_0_16, List.forall_mem_cons.2 ⟨subd16_0_17, List.forall_mem_cons.2 ⟨subd16_0_18, List.forall_mem_cons.2 ⟨subd16_0_19, List.forall_mem_cons.2 ⟨subd16_0_20, List.forall_mem_cons.2 ⟨subd16_0_21, List.forall_mem_cons.2 ⟨subd16_0_22, List.forall_mem_cons.2 ⟨subd16_0_23, List.forall_mem_cons.2 ⟨subd16_0_24, List.forall_mem_cons.2 ⟨subd16_0_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-1, -2] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-1, -1] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [-1, 0] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [-1, 1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [0, -2] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [0, -1] = true := by decide +kernel
theorem subd16_1_6 : subd16_1 [0, 0] = true := by decide +kernel
theorem subd16_1_7 : subd16_1 [0, 1] = true := by decide +kernel
theorem subd16_1_8 : subd16_1 [1, -2] = true := by decide +kernel
theorem subd16_1_9 : subd16_1 [1, -1] = true := by decide +kernel
theorem subd16_1_10 : subd16_1 [1, 0] = true := by decide +kernel
theorem subd16_1_11 : subd16_1 [1, 1] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_cons.2 ⟨subd16_1_6, List.forall_mem_cons.2 ⟨subd16_1_7, List.forall_mem_cons.2 ⟨subd16_1_8, List.forall_mem_cons.2 ⟨subd16_1_9, List.forall_mem_cons.2 ⟨subd16_1_10, List.forall_mem_cons.2 ⟨subd16_1_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [-2] = true := by decide +kernel
theorem subd17_0_1 : subd17_0 [-1] = true := by decide +kernel
theorem subd17_0_2 : subd17_0 [0] = true := by decide +kernel
theorem subd17_0_3 : subd17_0 [1] = true := by decide +kernel
theorem subd17_0_4 : subd17_0 [2] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_cons.2 ⟨subd17_0_1, List.forall_mem_cons.2 ⟨subd17_0_2, List.forall_mem_cons.2 ⟨subd17_0_3, List.forall_mem_cons.2 ⟨subd17_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [-2] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-1] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [0, -3] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [0, -2] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [0, -1] = true := by decide +kernel
theorem subd17_1_5 : subd17_1 [0, 0] = true := by decide +kernel
theorem subd17_1_6 : subd17_1 [0, 1] = true := by decide +kernel
theorem subd17_1_7 : subd17_1 [0, 2] = true := by decide +kernel
theorem subd17_1_8 : subd17_1 [1] = true := by decide +kernel
theorem subd17_1_9 : subd17_1 [2] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_cons.2 ⟨subd17_1_5, List.forall_mem_cons.2 ⟨subd17_1_6, List.forall_mem_cons.2 ⟨subd17_1_7, List.forall_mem_cons.2 ⟨subd17_1_8, List.forall_mem_cons.2 ⟨subd17_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [-2] = true := by decide +kernel
theorem subd18_0_1 : subd18_0 [-1] = true := by decide +kernel
theorem subd18_0_2 : subd18_0 [0] = true := by decide +kernel
theorem subd18_0_3 : subd18_0 [1] = true := by decide +kernel
theorem subd18_0_4 : subd18_0 [2] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_cons.2 ⟨subd18_0_1, List.forall_mem_cons.2 ⟨subd18_0_2, List.forall_mem_cons.2 ⟨subd18_0_3, List.forall_mem_cons.2 ⟨subd18_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [-2] = true := by decide +kernel
theorem subd18_1_1 : subd18_1 [-1] = true := by decide +kernel
theorem subd18_1_2 : subd18_1 [0] = true := by decide +kernel
theorem subd18_1_3 : subd18_1 [1] = true := by decide +kernel
theorem subd18_1_4 : subd18_1 [2] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_cons.2 ⟨subd18_1_1, List.forall_mem_cons.2 ⟨subd18_1_2, List.forall_mem_cons.2 ⟨subd18_1_3, List.forall_mem_cons.2 ⟨subd18_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
