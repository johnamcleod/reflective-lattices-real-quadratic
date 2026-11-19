import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_10 : ldCheck G d14_10.U d14_10.ms ldd14_10 = true := by decide +kernel
theorem pre_okd14_10 : subPre G cell14 d14_10 = true := by decide +kernel
theorem subd14_10_0 : subd14_10 [-2] = true := by decide +kernel
theorem subd14_10_1 : subd14_10 [-1] = true := by decide +kernel
theorem subd14_10_2 : subd14_10 [0] = true := by decide +kernel
theorem subd14_10_3 : subd14_10 [1] = true := by decide +kernel
theorem subd14_10_4 : subd14_10 [2] = true := by decide +kernel
theorem sbd14_10_0 : ∀ q ∈ blkd14_10_0, subd14_10 q = true := by
  unfold blkd14_10_0
  exact List.forall_mem_cons.2 ⟨subd14_10_0, List.forall_mem_cons.2 ⟨subd14_10_1, List.forall_mem_cons.2 ⟨subd14_10_2, List.forall_mem_cons.2 ⟨subd14_10_3, List.forall_mem_cons.2 ⟨subd14_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_11 : ldCheck G d14_11.U d14_11.ms ldd14_11 = true := by decide +kernel
theorem pre_okd14_11 : subPre G cell14 d14_11 = true := by decide +kernel
theorem subd14_11_0 : subd14_11 [] = true := by decide +kernel
theorem sbd14_11_0 : ∀ q ∈ blkd14_11_0, subd14_11 q = true := by
  unfold blkd14_11_0
  exact List.forall_mem_cons.2 ⟨subd14_11_0, List.forall_mem_nil _⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_nil _⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_nil _⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_nil _⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_nil _⟩
theorem ld_okd15_4 : ldCheck G d15_4.U d15_4.ms ldd15_4 = true := by decide +kernel
theorem pre_okd15_4 : subPre G cell15 d15_4 = true := by decide +kernel
theorem subd15_4_0 : subd15_4 [-3] = true := by decide +kernel
theorem subd15_4_1 : subd15_4 [-2] = true := by decide +kernel
theorem subd15_4_2 : subd15_4 [-1, -4] = true := by decide +kernel
theorem subd15_4_3 : subd15_4 [-1, -3] = true := by decide +kernel
theorem subd15_4_4 : subd15_4 [-1, -2] = true := by decide +kernel
theorem subd15_4_5 : subd15_4 [-1, -1] = true := by decide +kernel
theorem subd15_4_6 : subd15_4 [-1, 0] = true := by decide +kernel
theorem subd15_4_7 : subd15_4 [-1, 1] = true := by decide +kernel
theorem subd15_4_8 : subd15_4 [-1, 2] = true := by decide +kernel
theorem subd15_4_9 : subd15_4 [-1, 3] = true := by decide +kernel
theorem subd15_4_10 : subd15_4 [0, -4] = true := by decide +kernel
theorem subd15_4_11 : subd15_4 [0, -3] = true := by decide +kernel
theorem subd15_4_12 : subd15_4 [0, -2] = true := by decide +kernel
theorem subd15_4_13 : subd15_4 [0, -1] = true := by decide +kernel
theorem subd15_4_14 : subd15_4 [0, 0] = true := by decide +kernel
theorem subd15_4_15 : subd15_4 [0, 1] = true := by decide +kernel
theorem subd15_4_16 : subd15_4 [0, 2] = true := by decide +kernel
theorem subd15_4_17 : subd15_4 [0, 3] = true := by decide +kernel
theorem subd15_4_18 : subd15_4 [1, -4] = true := by decide +kernel
theorem subd15_4_19 : subd15_4 [1, -3] = true := by decide +kernel
theorem subd15_4_20 : subd15_4 [1, -2] = true := by decide +kernel
theorem subd15_4_21 : subd15_4 [1, -1] = true := by decide +kernel
theorem subd15_4_22 : subd15_4 [1, 0] = true := by decide +kernel
theorem subd15_4_23 : subd15_4 [1, 1] = true := by decide +kernel
theorem subd15_4_24 : subd15_4 [1, 2] = true := by decide +kernel
theorem subd15_4_25 : subd15_4 [1, 3] = true := by decide +kernel
theorem subd15_4_26 : subd15_4 [2] = true := by decide +kernel
theorem subd15_4_27 : subd15_4 [3] = true := by decide +kernel
theorem sbd15_4_0 : ∀ q ∈ blkd15_4_0, subd15_4 q = true := by
  unfold blkd15_4_0
  exact List.forall_mem_cons.2 ⟨subd15_4_0, List.forall_mem_cons.2 ⟨subd15_4_1, List.forall_mem_cons.2 ⟨subd15_4_2, List.forall_mem_cons.2 ⟨subd15_4_3, List.forall_mem_cons.2 ⟨subd15_4_4, List.forall_mem_cons.2 ⟨subd15_4_5, List.forall_mem_cons.2 ⟨subd15_4_6, List.forall_mem_cons.2 ⟨subd15_4_7, List.forall_mem_cons.2 ⟨subd15_4_8, List.forall_mem_cons.2 ⟨subd15_4_9, List.forall_mem_cons.2 ⟨subd15_4_10, List.forall_mem_cons.2 ⟨subd15_4_11, List.forall_mem_cons.2 ⟨subd15_4_12, List.forall_mem_cons.2 ⟨subd15_4_13, List.forall_mem_cons.2 ⟨subd15_4_14, List.forall_mem_cons.2 ⟨subd15_4_15, List.forall_mem_cons.2 ⟨subd15_4_16, List.forall_mem_cons.2 ⟨subd15_4_17, List.forall_mem_cons.2 ⟨subd15_4_18, List.forall_mem_cons.2 ⟨subd15_4_19, List.forall_mem_cons.2 ⟨subd15_4_20, List.forall_mem_cons.2 ⟨subd15_4_21, List.forall_mem_cons.2 ⟨subd15_4_22, List.forall_mem_cons.2 ⟨subd15_4_23, List.forall_mem_cons.2 ⟨subd15_4_24, List.forall_mem_cons.2 ⟨subd15_4_25, List.forall_mem_cons.2 ⟨subd15_4_26, List.forall_mem_cons.2 ⟨subd15_4_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
