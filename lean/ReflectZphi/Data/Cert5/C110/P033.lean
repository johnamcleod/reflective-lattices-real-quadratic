import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_nil _⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [0, -1] = true := by decide +kernel
theorem subd13_4_1 : subd13_4 [0, 0, -9] = true := by decide +kernel
theorem subd13_4_2 : subd13_4 [0, 0, -8] = true := by decide +kernel
theorem subd13_4_3 : subd13_4 [0, 0, -7] = true := by decide +kernel
theorem subd13_4_4 : subd13_4 [0, 0, -6] = true := by decide +kernel
theorem subd13_4_5 : subd13_4 [0, 0, -5] = true := by decide +kernel
theorem subd13_4_6 : subd13_4 [0, 0, -4] = true := by decide +kernel
theorem subd13_4_7 : subd13_4 [0, 0, -3] = true := by decide +kernel
theorem subd13_4_8 : subd13_4 [0, 0, -2] = true := by decide +kernel
theorem subd13_4_9 : subd13_4 [0, 0, -1] = true := by decide +kernel
theorem subd13_4_10 : subd13_4 [0, 0, 0] = true := by decide +kernel
theorem subd13_4_11 : subd13_4 [0, 0, 1] = true := by decide +kernel
theorem subd13_4_12 : subd13_4 [0, 0, 2] = true := by decide +kernel
theorem subd13_4_13 : subd13_4 [0, 0, 3] = true := by decide +kernel
theorem subd13_4_14 : subd13_4 [0, 0, 4] = true := by decide +kernel
theorem subd13_4_15 : subd13_4 [0, 0, 5] = true := by decide +kernel
theorem subd13_4_16 : subd13_4 [0, 0, 6] = true := by decide +kernel
theorem subd13_4_17 : subd13_4 [0, 0, 7] = true := by decide +kernel
theorem subd13_4_18 : subd13_4 [0, 0, 8] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_cons.2 ⟨subd13_4_1, List.forall_mem_cons.2 ⟨subd13_4_2, List.forall_mem_cons.2 ⟨subd13_4_3, List.forall_mem_cons.2 ⟨subd13_4_4, List.forall_mem_cons.2 ⟨subd13_4_5, List.forall_mem_cons.2 ⟨subd13_4_6, List.forall_mem_cons.2 ⟨subd13_4_7, List.forall_mem_cons.2 ⟨subd13_4_8, List.forall_mem_cons.2 ⟨subd13_4_9, List.forall_mem_cons.2 ⟨subd13_4_10, List.forall_mem_cons.2 ⟨subd13_4_11, List.forall_mem_cons.2 ⟨subd13_4_12, List.forall_mem_cons.2 ⟨subd13_4_13, List.forall_mem_cons.2 ⟨subd13_4_14, List.forall_mem_cons.2 ⟨subd13_4_15, List.forall_mem_cons.2 ⟨subd13_4_16, List.forall_mem_cons.2 ⟨subd13_4_17, List.forall_mem_cons.2 ⟨subd13_4_18, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
