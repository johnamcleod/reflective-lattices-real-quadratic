import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_8 : ldCheck G d13_8.U d13_8.ms ldd13_8 = true := by decide +kernel
theorem pre_okd13_8 : subPre G cell13 d13_8 = true := by decide +kernel
theorem subd13_8_0 : subd13_8 [-1, -2] = true := by decide +kernel
theorem subd13_8_1 : subd13_8 [-1, -1] = true := by decide +kernel
theorem subd13_8_2 : subd13_8 [-1, 0] = true := by decide +kernel
theorem subd13_8_3 : subd13_8 [-1, 1] = true := by decide +kernel
theorem subd13_8_4 : subd13_8 [0, -3] = true := by decide +kernel
theorem subd13_8_5 : subd13_8 [0, -2] = true := by decide +kernel
theorem subd13_8_6 : subd13_8 [0, -1] = true := by decide +kernel
theorem subd13_8_7 : subd13_8 [0, 0] = true := by decide +kernel
theorem subd13_8_8 : subd13_8 [0, 1] = true := by decide +kernel
theorem subd13_8_9 : subd13_8 [0, 2] = true := by decide +kernel
theorem subd13_8_10 : subd13_8 [1, -2] = true := by decide +kernel
theorem subd13_8_11 : subd13_8 [1, -1] = true := by decide +kernel
theorem subd13_8_12 : subd13_8 [1, 0] = true := by decide +kernel
theorem subd13_8_13 : subd13_8 [1, 1] = true := by decide +kernel
theorem sbd13_8_0 : ∀ q ∈ blkd13_8_0, subd13_8 q = true := by
  unfold blkd13_8_0
  exact List.forall_mem_cons.2 ⟨subd13_8_0, List.forall_mem_cons.2 ⟨subd13_8_1, List.forall_mem_cons.2 ⟨subd13_8_2, List.forall_mem_cons.2 ⟨subd13_8_3, List.forall_mem_cons.2 ⟨subd13_8_4, List.forall_mem_cons.2 ⟨subd13_8_5, List.forall_mem_cons.2 ⟨subd13_8_6, List.forall_mem_cons.2 ⟨subd13_8_7, List.forall_mem_cons.2 ⟨subd13_8_8, List.forall_mem_cons.2 ⟨subd13_8_9, List.forall_mem_cons.2 ⟨subd13_8_10, List.forall_mem_cons.2 ⟨subd13_8_11, List.forall_mem_cons.2 ⟨subd13_8_12, List.forall_mem_cons.2 ⟨subd13_8_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_9 : ldCheck G d13_9.U d13_9.ms ldd13_9 = true := by decide +kernel
theorem pre_okd13_9 : subPre G cell13 d13_9 = true := by decide +kernel
theorem subd13_9_0 : subd13_9 [] = true := by decide +kernel
theorem sbd13_9_0 : ∀ q ∈ blkd13_9_0, subd13_9 q = true := by
  unfold blkd13_9_0
  exact List.forall_mem_cons.2 ⟨subd13_9_0, List.forall_mem_nil _⟩
theorem ld_okd13_10 : ldCheck G d13_10.U d13_10.ms ldd13_10 = true := by decide +kernel
theorem pre_okd13_10 : subPre G cell13 d13_10 = true := by decide +kernel
theorem subd13_10_0 : subd13_10 [-1] = true := by decide +kernel
theorem subd13_10_1 : subd13_10 [0, -2] = true := by decide +kernel
theorem subd13_10_2 : subd13_10 [0, -1] = true := by decide +kernel
theorem subd13_10_3 : subd13_10 [0, 0] = true := by decide +kernel
theorem subd13_10_4 : subd13_10 [0, 1] = true := by decide +kernel
theorem subd13_10_5 : subd13_10 [1] = true := by decide +kernel
theorem sbd13_10_0 : ∀ q ∈ blkd13_10_0, subd13_10 q = true := by
  unfold blkd13_10_0
  exact List.forall_mem_cons.2 ⟨subd13_10_0, List.forall_mem_cons.2 ⟨subd13_10_1, List.forall_mem_cons.2 ⟨subd13_10_2, List.forall_mem_cons.2 ⟨subd13_10_3, List.forall_mem_cons.2 ⟨subd13_10_4, List.forall_mem_cons.2 ⟨subd13_10_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_11 : ldCheck G d13_11.U d13_11.ms ldd13_11 = true := by decide +kernel
theorem pre_okd13_11 : subPre G cell13 d13_11 = true := by decide +kernel
theorem subd13_11_0 : subd13_11 [] = true := by decide +kernel
theorem sbd13_11_0 : ∀ q ∈ blkd13_11_0, subd13_11 q = true := by
  unfold blkd13_11_0
  exact List.forall_mem_cons.2 ⟨subd13_11_0, List.forall_mem_nil _⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_nil _⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_nil _⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_nil _⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
