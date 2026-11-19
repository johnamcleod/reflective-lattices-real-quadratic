import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
theorem ld_okd0_2 : ldCheck G d0_2.U d0_2.ms ldd0_2 = true := by decide +kernel
theorem pre_okd0_2 : subPre G cell0 d0_2 = true := by decide +kernel
theorem subd0_2_0 : subd0_2 [-2] = true := by decide +kernel
theorem subd0_2_1 : subd0_2 [-1] = true := by decide +kernel
theorem subd0_2_2 : subd0_2 [0] = true := by decide +kernel
theorem subd0_2_3 : subd0_2 [1] = true := by decide +kernel
theorem subd0_2_4 : subd0_2 [2] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_cons.2 ⟨subd0_2_1, List.forall_mem_cons.2 ⟨subd0_2_2, List.forall_mem_cons.2 ⟨subd0_2_3, List.forall_mem_cons.2 ⟨subd0_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [-2] = true := by decide +kernel
theorem subd0_3_1 : subd0_3 [-1] = true := by decide +kernel
theorem subd0_3_2 : subd0_3 [0] = true := by decide +kernel
theorem subd0_3_3 : subd0_3 [1] = true := by decide +kernel
theorem subd0_3_4 : subd0_3 [2] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_cons.2 ⟨subd0_3_1, List.forall_mem_cons.2 ⟨subd0_3_2, List.forall_mem_cons.2 ⟨subd0_3_3, List.forall_mem_cons.2 ⟨subd0_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_4 : ldCheck G d0_4.U d0_4.ms ldd0_4 = true := by decide +kernel
theorem pre_okd0_4 : subPre G cell0 d0_4 = true := by decide +kernel
theorem subd0_4_0 : subd0_4 [-3] = true := by decide +kernel
theorem subd0_4_1 : subd0_4 [-2, -4] = true := by decide +kernel
theorem subd0_4_2 : subd0_4 [-2, -3] = true := by decide +kernel
theorem subd0_4_3 : subd0_4 [-2, -2] = true := by decide +kernel
theorem subd0_4_4 : subd0_4 [-2, -1] = true := by decide +kernel
theorem subd0_4_5 : subd0_4 [-2, 0] = true := by decide +kernel
theorem subd0_4_6 : subd0_4 [-2, 1] = true := by decide +kernel
theorem subd0_4_7 : subd0_4 [-2, 2] = true := by decide +kernel
theorem subd0_4_8 : subd0_4 [-1, -4] = true := by decide +kernel
theorem subd0_4_9 : subd0_4 [-1, -3] = true := by decide +kernel
theorem subd0_4_10 : subd0_4 [-1, -2] = true := by decide +kernel
theorem subd0_4_11 : subd0_4 [-1, -1] = true := by decide +kernel
theorem subd0_4_12 : subd0_4 [-1, 0] = true := by decide +kernel
theorem subd0_4_13 : subd0_4 [-1, 1] = true := by decide +kernel
theorem subd0_4_14 : subd0_4 [-1, 2] = true := by decide +kernel
theorem subd0_4_15 : subd0_4 [-1, 3] = true := by decide +kernel
theorem subd0_4_16 : subd0_4 [0, -4] = true := by decide +kernel
theorem subd0_4_17 : subd0_4 [0, -3] = true := by decide +kernel
theorem subd0_4_18 : subd0_4 [0, -2] = true := by decide +kernel
theorem subd0_4_19 : subd0_4 [0, -1] = true := by decide +kernel
theorem subd0_4_20 : subd0_4 [0, 0] = true := by decide +kernel
theorem subd0_4_21 : subd0_4 [0, 1] = true := by decide +kernel
theorem subd0_4_22 : subd0_4 [0, 2] = true := by decide +kernel
theorem subd0_4_23 : subd0_4 [0, 3] = true := by decide +kernel
theorem subd0_4_24 : subd0_4 [1, -4] = true := by decide +kernel
theorem subd0_4_25 : subd0_4 [1, -3] = true := by decide +kernel
theorem subd0_4_26 : subd0_4 [1, -2] = true := by decide +kernel
theorem subd0_4_27 : subd0_4 [1, -1] = true := by decide +kernel
theorem subd0_4_28 : subd0_4 [1, 0] = true := by decide +kernel
theorem subd0_4_29 : subd0_4 [1, 1] = true := by decide +kernel
theorem subd0_4_30 : subd0_4 [1, 2] = true := by decide +kernel
theorem subd0_4_31 : subd0_4 [1, 3] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_cons.2 ⟨subd0_4_1, List.forall_mem_cons.2 ⟨subd0_4_2, List.forall_mem_cons.2 ⟨subd0_4_3, List.forall_mem_cons.2 ⟨subd0_4_4, List.forall_mem_cons.2 ⟨subd0_4_5, List.forall_mem_cons.2 ⟨subd0_4_6, List.forall_mem_cons.2 ⟨subd0_4_7, List.forall_mem_cons.2 ⟨subd0_4_8, List.forall_mem_cons.2 ⟨subd0_4_9, List.forall_mem_cons.2 ⟨subd0_4_10, List.forall_mem_cons.2 ⟨subd0_4_11, List.forall_mem_cons.2 ⟨subd0_4_12, List.forall_mem_cons.2 ⟨subd0_4_13, List.forall_mem_cons.2 ⟨subd0_4_14, List.forall_mem_cons.2 ⟨subd0_4_15, List.forall_mem_cons.2 ⟨subd0_4_16, List.forall_mem_cons.2 ⟨subd0_4_17, List.forall_mem_cons.2 ⟨subd0_4_18, List.forall_mem_cons.2 ⟨subd0_4_19, List.forall_mem_cons.2 ⟨subd0_4_20, List.forall_mem_cons.2 ⟨subd0_4_21, List.forall_mem_cons.2 ⟨subd0_4_22, List.forall_mem_cons.2 ⟨subd0_4_23, List.forall_mem_cons.2 ⟨subd0_4_24, List.forall_mem_cons.2 ⟨subd0_4_25, List.forall_mem_cons.2 ⟨subd0_4_26, List.forall_mem_cons.2 ⟨subd0_4_27, List.forall_mem_cons.2 ⟨subd0_4_28, List.forall_mem_cons.2 ⟨subd0_4_29, List.forall_mem_cons.2 ⟨subd0_4_30, List.forall_mem_cons.2 ⟨subd0_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_4_32 : subd0_4 [2, -3] = true := by decide +kernel
theorem subd0_4_33 : subd0_4 [2, -2] = true := by decide +kernel
theorem subd0_4_34 : subd0_4 [2, -1] = true := by decide +kernel
theorem subd0_4_35 : subd0_4 [2, 0] = true := by decide +kernel
theorem subd0_4_36 : subd0_4 [2, 1] = true := by decide +kernel
theorem subd0_4_37 : subd0_4 [2, 2] = true := by decide +kernel
theorem subd0_4_38 : subd0_4 [2, 3] = true := by decide +kernel
theorem subd0_4_39 : subd0_4 [3] = true := by decide +kernel
theorem sbd0_4_1 : ∀ q ∈ blkd0_4_1, subd0_4 q = true := by
  unfold blkd0_4_1
  exact List.forall_mem_cons.2 ⟨subd0_4_32, List.forall_mem_cons.2 ⟨subd0_4_33, List.forall_mem_cons.2 ⟨subd0_4_34, List.forall_mem_cons.2 ⟨subd0_4_35, List.forall_mem_cons.2 ⟨subd0_4_36, List.forall_mem_cons.2 ⟨subd0_4_37, List.forall_mem_cons.2 ⟨subd0_4_38, List.forall_mem_cons.2 ⟨subd0_4_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_5 : ldCheck G d0_5.U d0_5.ms ldd0_5 = true := by decide +kernel
theorem pre_okd0_5 : subPre G cell0 d0_5 = true := by decide +kernel
theorem subd0_5_0 : subd0_5 [-1] = true := by decide +kernel
theorem subd0_5_1 : subd0_5 [0] = true := by decide +kernel
theorem subd0_5_2 : subd0_5 [1] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_cons.2 ⟨subd0_5_1, List.forall_mem_cons.2 ⟨subd0_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd0_6 : ldCheck G d0_6.U d0_6.ms ldd0_6 = true := by decide +kernel
theorem pre_okd0_6 : subPre G cell0 d0_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
