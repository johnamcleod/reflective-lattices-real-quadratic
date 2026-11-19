import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd28_1 : ldCheck G d28_1.U d28_1.ms ldd28_1 = true := by decide +kernel
theorem pre_okd28_1 : subPre G cell28 d28_1 = true := by decide +kernel
theorem subd28_1_0 : subd28_1 [-2] = true := by decide +kernel
theorem subd28_1_1 : subd28_1 [-1] = true := by decide +kernel
theorem subd28_1_2 : subd28_1 [0, -3] = true := by decide +kernel
theorem subd28_1_3 : subd28_1 [0, -2] = true := by decide +kernel
theorem subd28_1_4 : subd28_1 [0, -1] = true := by decide +kernel
theorem subd28_1_5 : subd28_1 [0, 0] = true := by decide +kernel
theorem subd28_1_6 : subd28_1 [0, 1] = true := by decide +kernel
theorem subd28_1_7 : subd28_1 [0, 2] = true := by decide +kernel
theorem subd28_1_8 : subd28_1 [1] = true := by decide +kernel
theorem subd28_1_9 : subd28_1 [2] = true := by decide +kernel
theorem sbd28_1_0 : ∀ q ∈ blkd28_1_0, subd28_1 q = true := by
  unfold blkd28_1_0
  exact List.forall_mem_cons.2 ⟨subd28_1_0, List.forall_mem_cons.2 ⟨subd28_1_1, List.forall_mem_cons.2 ⟨subd28_1_2, List.forall_mem_cons.2 ⟨subd28_1_3, List.forall_mem_cons.2 ⟨subd28_1_4, List.forall_mem_cons.2 ⟨subd28_1_5, List.forall_mem_cons.2 ⟨subd28_1_6, List.forall_mem_cons.2 ⟨subd28_1_7, List.forall_mem_cons.2 ⟨subd28_1_8, List.forall_mem_cons.2 ⟨subd28_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd28_2 : ldCheck G d28_2.U d28_2.ms ldd28_2 = true := by decide +kernel
theorem pre_okd28_2 : subPre G cell28 d28_2 = true := by decide +kernel
theorem subd28_2_0 : subd28_2 [-2] = true := by decide +kernel
theorem subd28_2_1 : subd28_2 [-1] = true := by decide +kernel
theorem subd28_2_2 : subd28_2 [0, -3] = true := by decide +kernel
theorem subd28_2_3 : subd28_2 [0, -2] = true := by decide +kernel
theorem subd28_2_4 : subd28_2 [0, -1] = true := by decide +kernel
theorem subd28_2_5 : subd28_2 [0, 0] = true := by decide +kernel
theorem subd28_2_6 : subd28_2 [0, 1] = true := by decide +kernel
theorem subd28_2_7 : subd28_2 [0, 2] = true := by decide +kernel
theorem subd28_2_8 : subd28_2 [1] = true := by decide +kernel
theorem subd28_2_9 : subd28_2 [2] = true := by decide +kernel
theorem sbd28_2_0 : ∀ q ∈ blkd28_2_0, subd28_2 q = true := by
  unfold blkd28_2_0
  exact List.forall_mem_cons.2 ⟨subd28_2_0, List.forall_mem_cons.2 ⟨subd28_2_1, List.forall_mem_cons.2 ⟨subd28_2_2, List.forall_mem_cons.2 ⟨subd28_2_3, List.forall_mem_cons.2 ⟨subd28_2_4, List.forall_mem_cons.2 ⟨subd28_2_5, List.forall_mem_cons.2 ⟨subd28_2_6, List.forall_mem_cons.2 ⟨subd28_2_7, List.forall_mem_cons.2 ⟨subd28_2_8, List.forall_mem_cons.2 ⟨subd28_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd28_3 : ldCheck G d28_3.U d28_3.ms ldd28_3 = true := by decide +kernel
theorem pre_okd28_3 : subPre G cell28 d28_3 = true := by decide +kernel
theorem subd28_3_0 : subd28_3 [-2] = true := by decide +kernel
theorem subd28_3_1 : subd28_3 [-1] = true := by decide +kernel
theorem subd28_3_2 : subd28_3 [0, -3] = true := by decide +kernel
theorem subd28_3_3 : subd28_3 [0, -2] = true := by decide +kernel
theorem subd28_3_4 : subd28_3 [0, -1] = true := by decide +kernel
theorem subd28_3_5 : subd28_3 [0, 0] = true := by decide +kernel
theorem subd28_3_6 : subd28_3 [0, 1] = true := by decide +kernel
theorem subd28_3_7 : subd28_3 [0, 2] = true := by decide +kernel
theorem subd28_3_8 : subd28_3 [1] = true := by decide +kernel
theorem subd28_3_9 : subd28_3 [2] = true := by decide +kernel
theorem sbd28_3_0 : ∀ q ∈ blkd28_3_0, subd28_3 q = true := by
  unfold blkd28_3_0
  exact List.forall_mem_cons.2 ⟨subd28_3_0, List.forall_mem_cons.2 ⟨subd28_3_1, List.forall_mem_cons.2 ⟨subd28_3_2, List.forall_mem_cons.2 ⟨subd28_3_3, List.forall_mem_cons.2 ⟨subd28_3_4, List.forall_mem_cons.2 ⟨subd28_3_5, List.forall_mem_cons.2 ⟨subd28_3_6, List.forall_mem_cons.2 ⟨subd28_3_7, List.forall_mem_cons.2 ⟨subd28_3_8, List.forall_mem_cons.2 ⟨subd28_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd29_0 : ldCheck G d29_0.U d29_0.ms ldd29_0 = true := by decide +kernel
theorem pre_okd29_0 : subPre G cell29 d29_0 = true := by decide +kernel
theorem subd29_0_0 : subd29_0 [-1] = true := by decide +kernel
theorem subd29_0_1 : subd29_0 [0, -2] = true := by decide +kernel
theorem subd29_0_2 : subd29_0 [0, -1] = true := by decide +kernel
theorem subd29_0_3 : subd29_0 [0, 0] = true := by decide +kernel
theorem subd29_0_4 : subd29_0 [0, 1] = true := by decide +kernel
theorem subd29_0_5 : subd29_0 [1] = true := by decide +kernel
theorem sbd29_0_0 : ∀ q ∈ blkd29_0_0, subd29_0 q = true := by
  unfold blkd29_0_0
  exact List.forall_mem_cons.2 ⟨subd29_0_0, List.forall_mem_cons.2 ⟨subd29_0_1, List.forall_mem_cons.2 ⟨subd29_0_2, List.forall_mem_cons.2 ⟨subd29_0_3, List.forall_mem_cons.2 ⟨subd29_0_4, List.forall_mem_cons.2 ⟨subd29_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd29_1 : ldCheck G d29_1.U d29_1.ms ldd29_1 = true := by decide +kernel
theorem pre_okd29_1 : subPre G cell29 d29_1 = true := by decide +kernel
theorem subd29_1_0 : subd29_1 [-2] = true := by decide +kernel
theorem subd29_1_1 : subd29_1 [-1, -3] = true := by decide +kernel
theorem subd29_1_2 : subd29_1 [-1, -2] = true := by decide +kernel
theorem subd29_1_3 : subd29_1 [-1, -1] = true := by decide +kernel
theorem subd29_1_4 : subd29_1 [-1, 0] = true := by decide +kernel
theorem subd29_1_5 : subd29_1 [-1, 1] = true := by decide +kernel
theorem subd29_1_6 : subd29_1 [-1, 2] = true := by decide +kernel
theorem subd29_1_7 : subd29_1 [0, -3] = true := by decide +kernel
theorem subd29_1_8 : subd29_1 [0, -2] = true := by decide +kernel
theorem subd29_1_9 : subd29_1 [0, -1] = true := by decide +kernel
theorem subd29_1_10 : subd29_1 [0, 0] = true := by decide +kernel
theorem subd29_1_11 : subd29_1 [0, 1] = true := by decide +kernel
theorem subd29_1_12 : subd29_1 [0, 2] = true := by decide +kernel
theorem subd29_1_13 : subd29_1 [1, -3] = true := by decide +kernel
theorem subd29_1_14 : subd29_1 [1, -2] = true := by decide +kernel
theorem subd29_1_15 : subd29_1 [1, -1] = true := by decide +kernel
theorem subd29_1_16 : subd29_1 [1, 0] = true := by decide +kernel
theorem subd29_1_17 : subd29_1 [1, 1] = true := by decide +kernel
theorem subd29_1_18 : subd29_1 [1, 2] = true := by decide +kernel
theorem subd29_1_19 : subd29_1 [2] = true := by decide +kernel
theorem sbd29_1_0 : ∀ q ∈ blkd29_1_0, subd29_1 q = true := by
  unfold blkd29_1_0
  exact List.forall_mem_cons.2 ⟨subd29_1_0, List.forall_mem_cons.2 ⟨subd29_1_1, List.forall_mem_cons.2 ⟨subd29_1_2, List.forall_mem_cons.2 ⟨subd29_1_3, List.forall_mem_cons.2 ⟨subd29_1_4, List.forall_mem_cons.2 ⟨subd29_1_5, List.forall_mem_cons.2 ⟨subd29_1_6, List.forall_mem_cons.2 ⟨subd29_1_7, List.forall_mem_cons.2 ⟨subd29_1_8, List.forall_mem_cons.2 ⟨subd29_1_9, List.forall_mem_cons.2 ⟨subd29_1_10, List.forall_mem_cons.2 ⟨subd29_1_11, List.forall_mem_cons.2 ⟨subd29_1_12, List.forall_mem_cons.2 ⟨subd29_1_13, List.forall_mem_cons.2 ⟨subd29_1_14, List.forall_mem_cons.2 ⟨subd29_1_15, List.forall_mem_cons.2 ⟨subd29_1_16, List.forall_mem_cons.2 ⟨subd29_1_17, List.forall_mem_cons.2 ⟨subd29_1_18, List.forall_mem_cons.2 ⟨subd29_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd29_2 : ldCheck G d29_2.U d29_2.ms ldd29_2 = true := by decide +kernel
theorem pre_okd29_2 : subPre G cell29 d29_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
