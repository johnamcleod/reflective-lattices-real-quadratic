import ReflectZphi.Data.Cert5.C087.Base

namespace ReflectZphi.Data.Cert5.C087

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_8_0 : subd0_8 [] = true := by decide +kernel
theorem sbd0_8_0 : ∀ q ∈ blkd0_8_0, subd0_8 q = true := by
  unfold blkd0_8_0
  exact List.forall_mem_cons.2 ⟨subd0_8_0, List.forall_mem_nil _⟩
theorem ld_okd0_9 : ldCheck G d0_9.U d0_9.ms ldd0_9 = true := by decide +kernel
theorem pre_okd0_9 : subPre G cell0 d0_9 = true := by decide +kernel
theorem subd0_9_0 : subd0_9 [-2] = true := by decide +kernel
theorem subd0_9_1 : subd0_9 [-1] = true := by decide +kernel
theorem subd0_9_2 : subd0_9 [0] = true := by decide +kernel
theorem subd0_9_3 : subd0_9 [1] = true := by decide +kernel
theorem subd0_9_4 : subd0_9 [2] = true := by decide +kernel
theorem sbd0_9_0 : ∀ q ∈ blkd0_9_0, subd0_9 q = true := by
  unfold blkd0_9_0
  exact List.forall_mem_cons.2 ⟨subd0_9_0, List.forall_mem_cons.2 ⟨subd0_9_1, List.forall_mem_cons.2 ⟨subd0_9_2, List.forall_mem_cons.2 ⟨subd0_9_3, List.forall_mem_cons.2 ⟨subd0_9_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_10 : ldCheck G d0_10.U d0_10.ms ldd0_10 = true := by decide +kernel
theorem pre_okd0_10 : subPre G cell0 d0_10 = true := by decide +kernel
theorem subd0_10_0 : subd0_10 [-2] = true := by decide +kernel
theorem subd0_10_1 : subd0_10 [-1] = true := by decide +kernel
theorem subd0_10_2 : subd0_10 [0, -3] = true := by decide +kernel
theorem subd0_10_3 : subd0_10 [0, -2] = true := by decide +kernel
theorem subd0_10_4 : subd0_10 [0, -1] = true := by decide +kernel
theorem subd0_10_5 : subd0_10 [0, 0] = true := by decide +kernel
theorem subd0_10_6 : subd0_10 [0, 1] = true := by decide +kernel
theorem subd0_10_7 : subd0_10 [0, 2] = true := by decide +kernel
theorem subd0_10_8 : subd0_10 [1] = true := by decide +kernel
theorem subd0_10_9 : subd0_10 [2] = true := by decide +kernel
theorem sbd0_10_0 : ∀ q ∈ blkd0_10_0, subd0_10 q = true := by
  unfold blkd0_10_0
  exact List.forall_mem_cons.2 ⟨subd0_10_0, List.forall_mem_cons.2 ⟨subd0_10_1, List.forall_mem_cons.2 ⟨subd0_10_2, List.forall_mem_cons.2 ⟨subd0_10_3, List.forall_mem_cons.2 ⟨subd0_10_4, List.forall_mem_cons.2 ⟨subd0_10_5, List.forall_mem_cons.2 ⟨subd0_10_6, List.forall_mem_cons.2 ⟨subd0_10_7, List.forall_mem_cons.2 ⟨subd0_10_8, List.forall_mem_cons.2 ⟨subd0_10_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_11 : ldCheck G d0_11.U d0_11.ms ldd0_11 = true := by decide +kernel
theorem pre_okd0_11 : subPre G cell0 d0_11 = true := by decide +kernel
theorem subd0_11_0 : subd0_11 [] = true := by decide +kernel
theorem sbd0_11_0 : ∀ q ∈ blkd0_11_0, subd0_11 q = true := by
  unfold blkd0_11_0
  exact List.forall_mem_cons.2 ⟨subd0_11_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C087
