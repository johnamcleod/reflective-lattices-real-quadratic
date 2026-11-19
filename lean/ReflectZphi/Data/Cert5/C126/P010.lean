import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-2] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-1] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [0] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [1] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [2] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-3] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [-1] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [0] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [1] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [2] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [3] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [-2] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-1] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [0, -1] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [1] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [2] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-1] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [0, -3] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [0, -2] = true := by decide +kernel
theorem subd9_7_3 : subd9_7 [0, -1] = true := by decide +kernel
theorem subd9_7_4 : subd9_7 [0, 0] = true := by decide +kernel
theorem subd9_7_5 : subd9_7 [0, 1] = true := by decide +kernel
theorem subd9_7_6 : subd9_7 [0, 2] = true := by decide +kernel
theorem subd9_7_7 : subd9_7 [1] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_cons.2 ⟨subd9_7_3, List.forall_mem_cons.2 ⟨subd9_7_4, List.forall_mem_cons.2 ⟨subd9_7_5, List.forall_mem_cons.2 ⟨subd9_7_6, List.forall_mem_cons.2 ⟨subd9_7_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [0] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C126
