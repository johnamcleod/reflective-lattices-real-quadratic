import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-2] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-1, -3] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [-1, -2] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [-1, -1] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [-1, 0] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [-1, 1] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [-1, 2] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [0, -3] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [0, -2] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [0, -1] = true := by decide +kernel
theorem subd14_0_10 : subd14_0 [0, 0] = true := by decide +kernel
theorem subd14_0_11 : subd14_0 [0, 1] = true := by decide +kernel
theorem subd14_0_12 : subd14_0 [0, 2] = true := by decide +kernel
theorem subd14_0_13 : subd14_0 [1, -3] = true := by decide +kernel
theorem subd14_0_14 : subd14_0 [1, -2] = true := by decide +kernel
theorem subd14_0_15 : subd14_0 [1, -1] = true := by decide +kernel
theorem subd14_0_16 : subd14_0 [1, 0] = true := by decide +kernel
theorem subd14_0_17 : subd14_0 [1, 1] = true := by decide +kernel
theorem subd14_0_18 : subd14_0 [1, 2] = true := by decide +kernel
theorem subd14_0_19 : subd14_0 [2] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_cons.2 ⟨subd14_0_10, List.forall_mem_cons.2 ⟨subd14_0_11, List.forall_mem_cons.2 ⟨subd14_0_12, List.forall_mem_cons.2 ⟨subd14_0_13, List.forall_mem_cons.2 ⟨subd14_0_14, List.forall_mem_cons.2 ⟨subd14_0_15, List.forall_mem_cons.2 ⟨subd14_0_16, List.forall_mem_cons.2 ⟨subd14_0_17, List.forall_mem_cons.2 ⟨subd14_0_18, List.forall_mem_cons.2 ⟨subd14_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-2] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-1] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [0] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [1] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [2] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-2] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-1, -3] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [-1, -2] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [-1, -1] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [-1, 0] = true := by decide +kernel
theorem subd14_2_5 : subd14_2 [-1, 1] = true := by decide +kernel
theorem subd14_2_6 : subd14_2 [-1, 2] = true := by decide +kernel
theorem subd14_2_7 : subd14_2 [0, -3] = true := by decide +kernel
theorem subd14_2_8 : subd14_2 [0, -2] = true := by decide +kernel
theorem subd14_2_9 : subd14_2 [0, -1] = true := by decide +kernel
theorem subd14_2_10 : subd14_2 [0, 0] = true := by decide +kernel
theorem subd14_2_11 : subd14_2 [0, 1] = true := by decide +kernel
theorem subd14_2_12 : subd14_2 [0, 2] = true := by decide +kernel
theorem subd14_2_13 : subd14_2 [1, -3] = true := by decide +kernel
theorem subd14_2_14 : subd14_2 [1, -2] = true := by decide +kernel
theorem subd14_2_15 : subd14_2 [1, -1] = true := by decide +kernel
theorem subd14_2_16 : subd14_2 [1, 0] = true := by decide +kernel
theorem subd14_2_17 : subd14_2 [1, 1] = true := by decide +kernel
theorem subd14_2_18 : subd14_2 [1, 2] = true := by decide +kernel
theorem subd14_2_19 : subd14_2 [2] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_cons.2 ⟨subd14_2_5, List.forall_mem_cons.2 ⟨subd14_2_6, List.forall_mem_cons.2 ⟨subd14_2_7, List.forall_mem_cons.2 ⟨subd14_2_8, List.forall_mem_cons.2 ⟨subd14_2_9, List.forall_mem_cons.2 ⟨subd14_2_10, List.forall_mem_cons.2 ⟨subd14_2_11, List.forall_mem_cons.2 ⟨subd14_2_12, List.forall_mem_cons.2 ⟨subd14_2_13, List.forall_mem_cons.2 ⟨subd14_2_14, List.forall_mem_cons.2 ⟨subd14_2_15, List.forall_mem_cons.2 ⟨subd14_2_16, List.forall_mem_cons.2 ⟨subd14_2_17, List.forall_mem_cons.2 ⟨subd14_2_18, List.forall_mem_cons.2 ⟨subd14_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_nil _⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-2] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-1, -3] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [-1, -2] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [-1, -1] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [-1, 0] = true := by decide +kernel
theorem subd15_0_5 : subd15_0 [-1, 1] = true := by decide +kernel
theorem subd15_0_6 : subd15_0 [-1, 2] = true := by decide +kernel
theorem subd15_0_7 : subd15_0 [0, -3] = true := by decide +kernel
theorem subd15_0_8 : subd15_0 [0, -2] = true := by decide +kernel
theorem subd15_0_9 : subd15_0 [0, -1] = true := by decide +kernel
theorem subd15_0_10 : subd15_0 [0, 0] = true := by decide +kernel
theorem subd15_0_11 : subd15_0 [0, 1] = true := by decide +kernel
theorem subd15_0_12 : subd15_0 [0, 2] = true := by decide +kernel
theorem subd15_0_13 : subd15_0 [1, -3] = true := by decide +kernel
theorem subd15_0_14 : subd15_0 [1, -2] = true := by decide +kernel
theorem subd15_0_15 : subd15_0 [1, -1] = true := by decide +kernel
theorem subd15_0_16 : subd15_0 [1, 0] = true := by decide +kernel
theorem subd15_0_17 : subd15_0 [1, 1] = true := by decide +kernel
theorem subd15_0_18 : subd15_0 [1, 2] = true := by decide +kernel
theorem subd15_0_19 : subd15_0 [2] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_cons.2 ⟨subd15_0_5, List.forall_mem_cons.2 ⟨subd15_0_6, List.forall_mem_cons.2 ⟨subd15_0_7, List.forall_mem_cons.2 ⟨subd15_0_8, List.forall_mem_cons.2 ⟨subd15_0_9, List.forall_mem_cons.2 ⟨subd15_0_10, List.forall_mem_cons.2 ⟨subd15_0_11, List.forall_mem_cons.2 ⟨subd15_0_12, List.forall_mem_cons.2 ⟨subd15_0_13, List.forall_mem_cons.2 ⟨subd15_0_14, List.forall_mem_cons.2 ⟨subd15_0_15, List.forall_mem_cons.2 ⟨subd15_0_16, List.forall_mem_cons.2 ⟨subd15_0_17, List.forall_mem_cons.2 ⟨subd15_0_18, List.forall_mem_cons.2 ⟨subd15_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C141
