import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_0 : subd8_4 [-1] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [0, -2] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [0, -1] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [0, 0] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [0, 1] = true := by decide +kernel
theorem subd8_4_5 : subd8_4 [1] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_cons.2 ⟨subd8_4_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_nil _⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-1] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [0] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [1] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_nil _⟩
theorem ld_okd8_8 : ldCheck G d8_8.U d8_8.ms ldd8_8 = true := by decide +kernel
theorem pre_okd8_8 : subPre G cell8 d8_8 = true := by decide +kernel
theorem subd8_8_0 : subd8_8 [-2] = true := by decide +kernel
theorem subd8_8_1 : subd8_8 [-1] = true := by decide +kernel
theorem subd8_8_2 : subd8_8 [0] = true := by decide +kernel
theorem subd8_8_3 : subd8_8 [1] = true := by decide +kernel
theorem subd8_8_4 : subd8_8 [2] = true := by decide +kernel
theorem sbd8_8_0 : ∀ q ∈ blkd8_8_0, subd8_8 q = true := by
  unfold blkd8_8_0
  exact List.forall_mem_cons.2 ⟨subd8_8_0, List.forall_mem_cons.2 ⟨subd8_8_1, List.forall_mem_cons.2 ⟨subd8_8_2, List.forall_mem_cons.2 ⟨subd8_8_3, List.forall_mem_cons.2 ⟨subd8_8_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_9 : ldCheck G d8_9.U d8_9.ms ldd8_9 = true := by decide +kernel
theorem pre_okd8_9 : subPre G cell8 d8_9 = true := by decide +kernel
theorem subd8_9_0 : subd8_9 [] = true := by decide +kernel
theorem sbd8_9_0 : ∀ q ∈ blkd8_9_0, subd8_9 q = true := by
  unfold blkd8_9_0
  exact List.forall_mem_cons.2 ⟨subd8_9_0, List.forall_mem_nil _⟩
theorem ld_okd8_10 : ldCheck G d8_10.U d8_10.ms ldd8_10 = true := by decide +kernel
theorem pre_okd8_10 : subPre G cell8 d8_10 = true := by decide +kernel
theorem subd8_10_0 : subd8_10 [-1] = true := by decide +kernel
theorem subd8_10_1 : subd8_10 [0] = true := by decide +kernel
theorem subd8_10_2 : subd8_10 [1] = true := by decide +kernel
theorem sbd8_10_0 : ∀ q ∈ blkd8_10_0, subd8_10 q = true := by
  unfold blkd8_10_0
  exact List.forall_mem_cons.2 ⟨subd8_10_0, List.forall_mem_cons.2 ⟨subd8_10_1, List.forall_mem_cons.2 ⟨subd8_10_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_11 : ldCheck G d8_11.U d8_11.ms ldd8_11 = true := by decide +kernel
theorem pre_okd8_11 : subPre G cell8 d8_11 = true := by decide +kernel
theorem subd8_11_0 : subd8_11 [] = true := by decide +kernel
theorem sbd8_11_0 : ∀ q ∈ blkd8_11_0, subd8_11 q = true := by
  unfold blkd8_11_0
  exact List.forall_mem_cons.2 ⟨subd8_11_0, List.forall_mem_nil _⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
