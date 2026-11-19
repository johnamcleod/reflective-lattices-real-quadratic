import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd26_3_0 : subd26_3 [-2] = true := by decide +kernel
theorem subd26_3_1 : subd26_3 [-1, -4] = true := by decide +kernel
theorem subd26_3_2 : subd26_3 [-1, -3] = true := by decide +kernel
theorem subd26_3_3 : subd26_3 [-1, -2] = true := by decide +kernel
theorem subd26_3_4 : subd26_3 [-1, -1] = true := by decide +kernel
theorem subd26_3_5 : subd26_3 [-1, 0] = true := by decide +kernel
theorem subd26_3_6 : subd26_3 [-1, 1] = true := by decide +kernel
theorem subd26_3_7 : subd26_3 [-1, 2] = true := by decide +kernel
theorem subd26_3_8 : subd26_3 [0, -4] = true := by decide +kernel
theorem subd26_3_9 : subd26_3 [0, -3] = true := by decide +kernel
theorem subd26_3_10 : subd26_3 [0, -2] = true := by decide +kernel
theorem subd26_3_11 : subd26_3 [0, -1] = true := by decide +kernel
theorem subd26_3_12 : subd26_3 [0, 0] = true := by decide +kernel
theorem subd26_3_13 : subd26_3 [0, 1] = true := by decide +kernel
theorem subd26_3_14 : subd26_3 [0, 2] = true := by decide +kernel
theorem subd26_3_15 : subd26_3 [0, 3] = true := by decide +kernel
theorem subd26_3_16 : subd26_3 [1, -3] = true := by decide +kernel
theorem subd26_3_17 : subd26_3 [1, -2] = true := by decide +kernel
theorem subd26_3_18 : subd26_3 [1, -1] = true := by decide +kernel
theorem subd26_3_19 : subd26_3 [1, 0] = true := by decide +kernel
theorem subd26_3_20 : subd26_3 [1, 1] = true := by decide +kernel
theorem subd26_3_21 : subd26_3 [1, 2] = true := by decide +kernel
theorem subd26_3_22 : subd26_3 [1, 3] = true := by decide +kernel
theorem subd26_3_23 : subd26_3 [2] = true := by decide +kernel
theorem sbd26_3_0 : ∀ q ∈ blkd26_3_0, subd26_3 q = true := by
  unfold blkd26_3_0
  exact List.forall_mem_cons.2 ⟨subd26_3_0, List.forall_mem_cons.2 ⟨subd26_3_1, List.forall_mem_cons.2 ⟨subd26_3_2, List.forall_mem_cons.2 ⟨subd26_3_3, List.forall_mem_cons.2 ⟨subd26_3_4, List.forall_mem_cons.2 ⟨subd26_3_5, List.forall_mem_cons.2 ⟨subd26_3_6, List.forall_mem_cons.2 ⟨subd26_3_7, List.forall_mem_cons.2 ⟨subd26_3_8, List.forall_mem_cons.2 ⟨subd26_3_9, List.forall_mem_cons.2 ⟨subd26_3_10, List.forall_mem_cons.2 ⟨subd26_3_11, List.forall_mem_cons.2 ⟨subd26_3_12, List.forall_mem_cons.2 ⟨subd26_3_13, List.forall_mem_cons.2 ⟨subd26_3_14, List.forall_mem_cons.2 ⟨subd26_3_15, List.forall_mem_cons.2 ⟨subd26_3_16, List.forall_mem_cons.2 ⟨subd26_3_17, List.forall_mem_cons.2 ⟨subd26_3_18, List.forall_mem_cons.2 ⟨subd26_3_19, List.forall_mem_cons.2 ⟨subd26_3_20, List.forall_mem_cons.2 ⟨subd26_3_21, List.forall_mem_cons.2 ⟨subd26_3_22, List.forall_mem_cons.2 ⟨subd26_3_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd27_0 : ldCheck G d27_0.U d27_0.ms ldd27_0 = true := by decide +kernel
theorem pre_okd27_0 : subPre G cell27 d27_0 = true := by decide +kernel
theorem subd27_0_0 : subd27_0 [-2] = true := by decide +kernel
theorem subd27_0_1 : subd27_0 [-1] = true := by decide +kernel
theorem subd27_0_2 : subd27_0 [0] = true := by decide +kernel
theorem subd27_0_3 : subd27_0 [1] = true := by decide +kernel
theorem subd27_0_4 : subd27_0 [2] = true := by decide +kernel
theorem sbd27_0_0 : ∀ q ∈ blkd27_0_0, subd27_0 q = true := by
  unfold blkd27_0_0
  exact List.forall_mem_cons.2 ⟨subd27_0_0, List.forall_mem_cons.2 ⟨subd27_0_1, List.forall_mem_cons.2 ⟨subd27_0_2, List.forall_mem_cons.2 ⟨subd27_0_3, List.forall_mem_cons.2 ⟨subd27_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd27_1 : ldCheck G d27_1.U d27_1.ms ldd27_1 = true := by decide +kernel
theorem pre_okd27_1 : subPre G cell27 d27_1 = true := by decide +kernel
theorem subd27_1_0 : subd27_1 [-2] = true := by decide +kernel
theorem subd27_1_1 : subd27_1 [-1, -3] = true := by decide +kernel
theorem subd27_1_2 : subd27_1 [-1, -2] = true := by decide +kernel
theorem subd27_1_3 : subd27_1 [-1, -1] = true := by decide +kernel
theorem subd27_1_4 : subd27_1 [-1, 0] = true := by decide +kernel
theorem subd27_1_5 : subd27_1 [-1, 1] = true := by decide +kernel
theorem subd27_1_6 : subd27_1 [0, -2] = true := by decide +kernel
theorem subd27_1_7 : subd27_1 [0, -1] = true := by decide +kernel
theorem subd27_1_8 : subd27_1 [0, 0] = true := by decide +kernel
theorem subd27_1_9 : subd27_1 [0, 1] = true := by decide +kernel
theorem subd27_1_10 : subd27_1 [1, -2] = true := by decide +kernel
theorem subd27_1_11 : subd27_1 [1, -1] = true := by decide +kernel
theorem subd27_1_12 : subd27_1 [1, 0] = true := by decide +kernel
theorem subd27_1_13 : subd27_1 [1, 1] = true := by decide +kernel
theorem subd27_1_14 : subd27_1 [1, 2] = true := by decide +kernel
theorem subd27_1_15 : subd27_1 [2] = true := by decide +kernel
theorem sbd27_1_0 : ∀ q ∈ blkd27_1_0, subd27_1 q = true := by
  unfold blkd27_1_0
  exact List.forall_mem_cons.2 ⟨subd27_1_0, List.forall_mem_cons.2 ⟨subd27_1_1, List.forall_mem_cons.2 ⟨subd27_1_2, List.forall_mem_cons.2 ⟨subd27_1_3, List.forall_mem_cons.2 ⟨subd27_1_4, List.forall_mem_cons.2 ⟨subd27_1_5, List.forall_mem_cons.2 ⟨subd27_1_6, List.forall_mem_cons.2 ⟨subd27_1_7, List.forall_mem_cons.2 ⟨subd27_1_8, List.forall_mem_cons.2 ⟨subd27_1_9, List.forall_mem_cons.2 ⟨subd27_1_10, List.forall_mem_cons.2 ⟨subd27_1_11, List.forall_mem_cons.2 ⟨subd27_1_12, List.forall_mem_cons.2 ⟨subd27_1_13, List.forall_mem_cons.2 ⟨subd27_1_14, List.forall_mem_cons.2 ⟨subd27_1_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd27_2 : ldCheck G d27_2.U d27_2.ms ldd27_2 = true := by decide +kernel
theorem pre_okd27_2 : subPre G cell27 d27_2 = true := by decide +kernel
theorem subd27_2_0 : subd27_2 [-1] = true := by decide +kernel
theorem subd27_2_1 : subd27_2 [0, -2] = true := by decide +kernel
theorem subd27_2_2 : subd27_2 [0, -1] = true := by decide +kernel
theorem subd27_2_3 : subd27_2 [0, 0] = true := by decide +kernel
theorem subd27_2_4 : subd27_2 [0, 1] = true := by decide +kernel
theorem subd27_2_5 : subd27_2 [1] = true := by decide +kernel
theorem sbd27_2_0 : ∀ q ∈ blkd27_2_0, subd27_2 q = true := by
  unfold blkd27_2_0
  exact List.forall_mem_cons.2 ⟨subd27_2_0, List.forall_mem_cons.2 ⟨subd27_2_1, List.forall_mem_cons.2 ⟨subd27_2_2, List.forall_mem_cons.2 ⟨subd27_2_3, List.forall_mem_cons.2 ⟨subd27_2_4, List.forall_mem_cons.2 ⟨subd27_2_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd27_3 : ldCheck G d27_3.U d27_3.ms ldd27_3 = true := by decide +kernel
theorem pre_okd27_3 : subPre G cell27 d27_3 = true := by decide +kernel
theorem subd27_3_0 : subd27_3 [-3] = true := by decide +kernel
theorem subd27_3_1 : subd27_3 [-2] = true := by decide +kernel
theorem subd27_3_2 : subd27_3 [-1] = true := by decide +kernel
theorem subd27_3_3 : subd27_3 [0] = true := by decide +kernel
theorem subd27_3_4 : subd27_3 [1] = true := by decide +kernel
theorem subd27_3_5 : subd27_3 [2] = true := by decide +kernel
theorem subd27_3_6 : subd27_3 [3] = true := by decide +kernel
theorem sbd27_3_0 : ∀ q ∈ blkd27_3_0, subd27_3 q = true := by
  unfold blkd27_3_0
  exact List.forall_mem_cons.2 ⟨subd27_3_0, List.forall_mem_cons.2 ⟨subd27_3_1, List.forall_mem_cons.2 ⟨subd27_3_2, List.forall_mem_cons.2 ⟨subd27_3_3, List.forall_mem_cons.2 ⟨subd27_3_4, List.forall_mem_cons.2 ⟨subd27_3_5, List.forall_mem_cons.2 ⟨subd27_3_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd28_0 : ldCheck G d28_0.U d28_0.ms ldd28_0 = true := by decide +kernel
theorem pre_okd28_0 : subPre G cell28 d28_0 = true := by decide +kernel
theorem subd28_0_0 : subd28_0 [-2] = true := by decide +kernel
theorem subd28_0_1 : subd28_0 [-1] = true := by decide +kernel
theorem subd28_0_2 : subd28_0 [0] = true := by decide +kernel
theorem subd28_0_3 : subd28_0 [1] = true := by decide +kernel
theorem subd28_0_4 : subd28_0 [2] = true := by decide +kernel
theorem sbd28_0_0 : ∀ q ∈ blkd28_0_0, subd28_0 q = true := by
  unfold blkd28_0_0
  exact List.forall_mem_cons.2 ⟨subd28_0_0, List.forall_mem_cons.2 ⟨subd28_0_1, List.forall_mem_cons.2 ⟨subd28_0_2, List.forall_mem_cons.2 ⟨subd28_0_3, List.forall_mem_cons.2 ⟨subd28_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
