import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_5_0 : subd8_5 [-2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [0, -4] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [0, -3] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_8 : subd8_5 [0, 2] = true := by decide +kernel
theorem subd8_5_9 : subd8_5 [0, 3] = true := by decide +kernel
theorem subd8_5_10 : subd8_5 [1] = true := by decide +kernel
theorem subd8_5_11 : subd8_5 [2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_cons.2 ⟨subd8_5_8, List.forall_mem_cons.2 ⟨subd8_5_9, List.forall_mem_cons.2 ⟨subd8_5_10, List.forall_mem_cons.2 ⟨subd8_5_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-3] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-2] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-1] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [0] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [1] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [2] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [3] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [-2] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-1] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [0] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [1] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [2] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_nil _⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_nil _⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-2] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-1] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [1] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [2] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C126
