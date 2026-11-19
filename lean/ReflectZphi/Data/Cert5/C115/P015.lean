import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [0] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [1] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-2] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-1] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [0, -3] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [0, -2] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [0, -1] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [0, 0] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [0, 1] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [0, 2] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [1] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [2] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-2] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-1] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [0] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [1] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [2] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_8 : ldCheck G d10_8.U d10_8.ms ldd10_8 = true := by decide +kernel
theorem pre_okd10_8 : subPre G cell10 d10_8 = true := by decide +kernel
theorem subd10_8_0 : subd10_8 [-2] = true := by decide +kernel
theorem subd10_8_1 : subd10_8 [-1] = true := by decide +kernel
theorem subd10_8_2 : subd10_8 [0, -3] = true := by decide +kernel
theorem subd10_8_3 : subd10_8 [0, -2] = true := by decide +kernel
theorem subd10_8_4 : subd10_8 [0, -1] = true := by decide +kernel
theorem subd10_8_5 : subd10_8 [0, 0] = true := by decide +kernel
theorem subd10_8_6 : subd10_8 [0, 1] = true := by decide +kernel
theorem subd10_8_7 : subd10_8 [0, 2] = true := by decide +kernel
theorem subd10_8_8 : subd10_8 [1] = true := by decide +kernel
theorem subd10_8_9 : subd10_8 [2] = true := by decide +kernel
theorem sbd10_8_0 : ∀ q ∈ blkd10_8_0, subd10_8 q = true := by
  unfold blkd10_8_0
  exact List.forall_mem_cons.2 ⟨subd10_8_0, List.forall_mem_cons.2 ⟨subd10_8_1, List.forall_mem_cons.2 ⟨subd10_8_2, List.forall_mem_cons.2 ⟨subd10_8_3, List.forall_mem_cons.2 ⟨subd10_8_4, List.forall_mem_cons.2 ⟨subd10_8_5, List.forall_mem_cons.2 ⟨subd10_8_6, List.forall_mem_cons.2 ⟨subd10_8_7, List.forall_mem_cons.2 ⟨subd10_8_8, List.forall_mem_cons.2 ⟨subd10_8_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_9 : ldCheck G d10_9.U d10_9.ms ldd10_9 = true := by decide +kernel
theorem pre_okd10_9 : subPre G cell10 d10_9 = true := by decide +kernel
theorem subd10_9_0 : subd10_9 [] = true := by decide +kernel
theorem sbd10_9_0 : ∀ q ∈ blkd10_9_0, subd10_9 q = true := by
  unfold blkd10_9_0
  exact List.forall_mem_cons.2 ⟨subd10_9_0, List.forall_mem_nil _⟩
theorem ld_okd10_10 : ldCheck G d10_10.U d10_10.ms ldd10_10 = true := by decide +kernel
theorem pre_okd10_10 : subPre G cell10 d10_10 = true := by decide +kernel
theorem subd10_10_0 : subd10_10 [-2] = true := by decide +kernel
theorem subd10_10_1 : subd10_10 [-1] = true := by decide +kernel
theorem subd10_10_2 : subd10_10 [0] = true := by decide +kernel
theorem subd10_10_3 : subd10_10 [1] = true := by decide +kernel
theorem subd10_10_4 : subd10_10 [2] = true := by decide +kernel
theorem sbd10_10_0 : ∀ q ∈ blkd10_10_0, subd10_10 q = true := by
  unfold blkd10_10_0
  exact List.forall_mem_cons.2 ⟨subd10_10_0, List.forall_mem_cons.2 ⟨subd10_10_1, List.forall_mem_cons.2 ⟨subd10_10_2, List.forall_mem_cons.2 ⟨subd10_10_3, List.forall_mem_cons.2 ⟨subd10_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_11 : ldCheck G d10_11.U d10_11.ms ldd10_11 = true := by decide +kernel
theorem pre_okd10_11 : subPre G cell10 d10_11 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
