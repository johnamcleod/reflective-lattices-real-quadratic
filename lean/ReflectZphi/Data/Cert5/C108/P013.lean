import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [1] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [0, 0] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [1] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [0, 0, -8] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [0, 0, -7] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [0, 0, -6] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [0, 0, -5] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [0, 0, -4] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [0, 0, -3] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [0, 0, -2] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [0, 0, -1] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [0, 0, 0] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [0, 0, 1] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [0, 0, 2] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [0, 0, 3] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [0, 0, 4] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [0, 0, 5] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [0, 0, 6] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [0, 0, 7] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [1] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [0] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [1, 1] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-2] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [0] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [1] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [2] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C108
