import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_5_0 : subd14_5 [-2] = true := by decide +kernel
theorem subd14_5_1 : subd14_5 [-1, -3] = true := by decide +kernel
theorem subd14_5_2 : subd14_5 [-1, -2] = true := by decide +kernel
theorem subd14_5_3 : subd14_5 [-1, -1] = true := by decide +kernel
theorem subd14_5_4 : subd14_5 [-1, 0] = true := by decide +kernel
theorem subd14_5_5 : subd14_5 [-1, 1] = true := by decide +kernel
theorem subd14_5_6 : subd14_5 [-1, 2] = true := by decide +kernel
theorem subd14_5_7 : subd14_5 [-1, 3] = true := by decide +kernel
theorem subd14_5_8 : subd14_5 [0, -3] = true := by decide +kernel
theorem subd14_5_9 : subd14_5 [0, -2] = true := by decide +kernel
theorem subd14_5_10 : subd14_5 [0, -1] = true := by decide +kernel
theorem subd14_5_11 : subd14_5 [0, 0] = true := by decide +kernel
theorem subd14_5_12 : subd14_5 [0, 1] = true := by decide +kernel
theorem subd14_5_13 : subd14_5 [0, 2] = true := by decide +kernel
theorem subd14_5_14 : subd14_5 [1, -4] = true := by decide +kernel
theorem subd14_5_15 : subd14_5 [1, -3] = true := by decide +kernel
theorem subd14_5_16 : subd14_5 [1, -2] = true := by decide +kernel
theorem subd14_5_17 : subd14_5 [1, -1] = true := by decide +kernel
theorem subd14_5_18 : subd14_5 [1, 0] = true := by decide +kernel
theorem subd14_5_19 : subd14_5 [1, 1] = true := by decide +kernel
theorem subd14_5_20 : subd14_5 [1, 2] = true := by decide +kernel
theorem subd14_5_21 : subd14_5 [2] = true := by decide +kernel
theorem sbd14_5_0 : ∀ q ∈ blkd14_5_0, subd14_5 q = true := by
  unfold blkd14_5_0
  exact List.forall_mem_cons.2 ⟨subd14_5_0, List.forall_mem_cons.2 ⟨subd14_5_1, List.forall_mem_cons.2 ⟨subd14_5_2, List.forall_mem_cons.2 ⟨subd14_5_3, List.forall_mem_cons.2 ⟨subd14_5_4, List.forall_mem_cons.2 ⟨subd14_5_5, List.forall_mem_cons.2 ⟨subd14_5_6, List.forall_mem_cons.2 ⟨subd14_5_7, List.forall_mem_cons.2 ⟨subd14_5_8, List.forall_mem_cons.2 ⟨subd14_5_9, List.forall_mem_cons.2 ⟨subd14_5_10, List.forall_mem_cons.2 ⟨subd14_5_11, List.forall_mem_cons.2 ⟨subd14_5_12, List.forall_mem_cons.2 ⟨subd14_5_13, List.forall_mem_cons.2 ⟨subd14_5_14, List.forall_mem_cons.2 ⟨subd14_5_15, List.forall_mem_cons.2 ⟨subd14_5_16, List.forall_mem_cons.2 ⟨subd14_5_17, List.forall_mem_cons.2 ⟨subd14_5_18, List.forall_mem_cons.2 ⟨subd14_5_19, List.forall_mem_cons.2 ⟨subd14_5_20, List.forall_mem_cons.2 ⟨subd14_5_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_6 : ldCheck G d14_6.U d14_6.ms ldd14_6 = true := by decide +kernel
theorem pre_okd14_6 : subPre G cell14 d14_6 = true := by decide +kernel
theorem subd14_6_0 : subd14_6 [-2] = true := by decide +kernel
theorem subd14_6_1 : subd14_6 [-1] = true := by decide +kernel
theorem subd14_6_2 : subd14_6 [0, -3] = true := by decide +kernel
theorem subd14_6_3 : subd14_6 [0, -2] = true := by decide +kernel
theorem subd14_6_4 : subd14_6 [0, -1] = true := by decide +kernel
theorem subd14_6_5 : subd14_6 [0, 0] = true := by decide +kernel
theorem subd14_6_6 : subd14_6 [0, 1] = true := by decide +kernel
theorem subd14_6_7 : subd14_6 [0, 2] = true := by decide +kernel
theorem subd14_6_8 : subd14_6 [1] = true := by decide +kernel
theorem subd14_6_9 : subd14_6 [2] = true := by decide +kernel
theorem sbd14_6_0 : ∀ q ∈ blkd14_6_0, subd14_6 q = true := by
  unfold blkd14_6_0
  exact List.forall_mem_cons.2 ⟨subd14_6_0, List.forall_mem_cons.2 ⟨subd14_6_1, List.forall_mem_cons.2 ⟨subd14_6_2, List.forall_mem_cons.2 ⟨subd14_6_3, List.forall_mem_cons.2 ⟨subd14_6_4, List.forall_mem_cons.2 ⟨subd14_6_5, List.forall_mem_cons.2 ⟨subd14_6_6, List.forall_mem_cons.2 ⟨subd14_6_7, List.forall_mem_cons.2 ⟨subd14_6_8, List.forall_mem_cons.2 ⟨subd14_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_7 : ldCheck G d14_7.U d14_7.ms ldd14_7 = true := by decide +kernel
theorem pre_okd14_7 : subPre G cell14 d14_7 = true := by decide +kernel
theorem subd14_7_0 : subd14_7 [-2] = true := by decide +kernel
theorem subd14_7_1 : subd14_7 [-1] = true := by decide +kernel
theorem subd14_7_2 : subd14_7 [0, -3] = true := by decide +kernel
theorem subd14_7_3 : subd14_7 [0, -2] = true := by decide +kernel
theorem subd14_7_4 : subd14_7 [0, -1] = true := by decide +kernel
theorem subd14_7_5 : subd14_7 [0, 0] = true := by decide +kernel
theorem subd14_7_6 : subd14_7 [0, 1] = true := by decide +kernel
theorem subd14_7_7 : subd14_7 [0, 2] = true := by decide +kernel
theorem subd14_7_8 : subd14_7 [1] = true := by decide +kernel
theorem subd14_7_9 : subd14_7 [2] = true := by decide +kernel
theorem sbd14_7_0 : ∀ q ∈ blkd14_7_0, subd14_7 q = true := by
  unfold blkd14_7_0
  exact List.forall_mem_cons.2 ⟨subd14_7_0, List.forall_mem_cons.2 ⟨subd14_7_1, List.forall_mem_cons.2 ⟨subd14_7_2, List.forall_mem_cons.2 ⟨subd14_7_3, List.forall_mem_cons.2 ⟨subd14_7_4, List.forall_mem_cons.2 ⟨subd14_7_5, List.forall_mem_cons.2 ⟨subd14_7_6, List.forall_mem_cons.2 ⟨subd14_7_7, List.forall_mem_cons.2 ⟨subd14_7_8, List.forall_mem_cons.2 ⟨subd14_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [-1] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [0] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [1] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-2] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-1, -3] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-1, -1] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-1, 0] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-1, 2] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [0, -3] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [0, -1] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [0, 0] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [0, 1] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [0, 2] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [1, -3] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [1, 0] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [1, 1] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [1, 2] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [2] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
