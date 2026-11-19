import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_1_0 : subd14_1 [-3] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-2, -3] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-2, -2] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-2, -1] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-2, 0] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-2, 1] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-1, -3] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-1, -1] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-1, 0] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-1, 1] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-1, 2] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [0, -1] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [1, -3] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [1, -2] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [1, -1] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [1, 0] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [1, 1] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [1, 2] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [2, -2] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [2, -1] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [2, 0] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [2, 1] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [2, 2] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [3] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-2] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-1] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [0] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [1] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [2] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-2] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-1, -3] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [-1, -2] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [-1, -1] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [-1, 0] = true := by decide +kernel
theorem subd14_3_5 : subd14_3 [-1, 1] = true := by decide +kernel
theorem subd14_3_6 : subd14_3 [-1, 2] = true := by decide +kernel
theorem subd14_3_7 : subd14_3 [0, -3] = true := by decide +kernel
theorem subd14_3_8 : subd14_3 [0, -2] = true := by decide +kernel
theorem subd14_3_9 : subd14_3 [0, -1] = true := by decide +kernel
theorem subd14_3_10 : subd14_3 [0, 0] = true := by decide +kernel
theorem subd14_3_11 : subd14_3 [0, 1] = true := by decide +kernel
theorem subd14_3_12 : subd14_3 [0, 2] = true := by decide +kernel
theorem subd14_3_13 : subd14_3 [1, -3] = true := by decide +kernel
theorem subd14_3_14 : subd14_3 [1, -2] = true := by decide +kernel
theorem subd14_3_15 : subd14_3 [1, -1] = true := by decide +kernel
theorem subd14_3_16 : subd14_3 [1, 0] = true := by decide +kernel
theorem subd14_3_17 : subd14_3 [1, 1] = true := by decide +kernel
theorem subd14_3_18 : subd14_3 [1, 2] = true := by decide +kernel
theorem subd14_3_19 : subd14_3 [2] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_cons.2 ⟨subd14_3_5, List.forall_mem_cons.2 ⟨subd14_3_6, List.forall_mem_cons.2 ⟨subd14_3_7, List.forall_mem_cons.2 ⟨subd14_3_8, List.forall_mem_cons.2 ⟨subd14_3_9, List.forall_mem_cons.2 ⟨subd14_3_10, List.forall_mem_cons.2 ⟨subd14_3_11, List.forall_mem_cons.2 ⟨subd14_3_12, List.forall_mem_cons.2 ⟨subd14_3_13, List.forall_mem_cons.2 ⟨subd14_3_14, List.forall_mem_cons.2 ⟨subd14_3_15, List.forall_mem_cons.2 ⟨subd14_3_16, List.forall_mem_cons.2 ⟨subd14_3_17, List.forall_mem_cons.2 ⟨subd14_3_18, List.forall_mem_cons.2 ⟨subd14_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_nil _⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-3] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-2] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-1] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [0] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [1] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [2] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [3] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-1] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [0] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [1] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
