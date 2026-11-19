import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_0 : subd14_0 [-1] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [0] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [1] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-2] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-1] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [0, -1] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [1] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [2] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-1] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [0] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [1] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-2] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-1] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [0] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [1] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [2] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-2] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-1] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [0] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [1] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [2] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-2] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-1] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [0] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [1] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [2] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-1] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [0] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [1] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C130
