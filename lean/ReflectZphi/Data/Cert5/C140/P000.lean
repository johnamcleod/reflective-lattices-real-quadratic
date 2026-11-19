import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

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
theorem subd0_2_0 : subd0_2 [] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_nil _⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [-3] = true := by decide +kernel
theorem subd0_3_1 : subd0_3 [-2, -3] = true := by decide +kernel
theorem subd0_3_2 : subd0_3 [-2, -2] = true := by decide +kernel
theorem subd0_3_3 : subd0_3 [-2, -1] = true := by decide +kernel
theorem subd0_3_4 : subd0_3 [-2, 0] = true := by decide +kernel
theorem subd0_3_5 : subd0_3 [-2, 1] = true := by decide +kernel
theorem subd0_3_6 : subd0_3 [-2, 2] = true := by decide +kernel
theorem subd0_3_7 : subd0_3 [-2, 3] = true := by decide +kernel
theorem subd0_3_8 : subd0_3 [-1, -4] = true := by decide +kernel
theorem subd0_3_9 : subd0_3 [-1, -3] = true := by decide +kernel
theorem subd0_3_10 : subd0_3 [-1, -2] = true := by decide +kernel
theorem subd0_3_11 : subd0_3 [-1, -1] = true := by decide +kernel
theorem subd0_3_12 : subd0_3 [-1, 0] = true := by decide +kernel
theorem subd0_3_13 : subd0_3 [-1, 1] = true := by decide +kernel
theorem subd0_3_14 : subd0_3 [-1, 2] = true := by decide +kernel
theorem subd0_3_15 : subd0_3 [-1, 3] = true := by decide +kernel
theorem subd0_3_16 : subd0_3 [0, -4] = true := by decide +kernel
theorem subd0_3_17 : subd0_3 [0, -3] = true := by decide +kernel
theorem subd0_3_18 : subd0_3 [0, -2] = true := by decide +kernel
theorem subd0_3_19 : subd0_3 [0, -1] = true := by decide +kernel
theorem subd0_3_20 : subd0_3 [0, 0] = true := by decide +kernel
theorem subd0_3_21 : subd0_3 [0, 1] = true := by decide +kernel
theorem subd0_3_22 : subd0_3 [0, 2] = true := by decide +kernel
theorem subd0_3_23 : subd0_3 [0, 3] = true := by decide +kernel
theorem subd0_3_24 : subd0_3 [1, -4] = true := by decide +kernel
theorem subd0_3_25 : subd0_3 [1, -3] = true := by decide +kernel
theorem subd0_3_26 : subd0_3 [1, -2] = true := by decide +kernel
theorem subd0_3_27 : subd0_3 [1, -1] = true := by decide +kernel
theorem subd0_3_28 : subd0_3 [1, 0] = true := by decide +kernel
theorem subd0_3_29 : subd0_3 [1, 1] = true := by decide +kernel
theorem subd0_3_30 : subd0_3 [1, 2] = true := by decide +kernel
theorem subd0_3_31 : subd0_3 [1, 3] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_cons.2 ⟨subd0_3_1, List.forall_mem_cons.2 ⟨subd0_3_2, List.forall_mem_cons.2 ⟨subd0_3_3, List.forall_mem_cons.2 ⟨subd0_3_4, List.forall_mem_cons.2 ⟨subd0_3_5, List.forall_mem_cons.2 ⟨subd0_3_6, List.forall_mem_cons.2 ⟨subd0_3_7, List.forall_mem_cons.2 ⟨subd0_3_8, List.forall_mem_cons.2 ⟨subd0_3_9, List.forall_mem_cons.2 ⟨subd0_3_10, List.forall_mem_cons.2 ⟨subd0_3_11, List.forall_mem_cons.2 ⟨subd0_3_12, List.forall_mem_cons.2 ⟨subd0_3_13, List.forall_mem_cons.2 ⟨subd0_3_14, List.forall_mem_cons.2 ⟨subd0_3_15, List.forall_mem_cons.2 ⟨subd0_3_16, List.forall_mem_cons.2 ⟨subd0_3_17, List.forall_mem_cons.2 ⟨subd0_3_18, List.forall_mem_cons.2 ⟨subd0_3_19, List.forall_mem_cons.2 ⟨subd0_3_20, List.forall_mem_cons.2 ⟨subd0_3_21, List.forall_mem_cons.2 ⟨subd0_3_22, List.forall_mem_cons.2 ⟨subd0_3_23, List.forall_mem_cons.2 ⟨subd0_3_24, List.forall_mem_cons.2 ⟨subd0_3_25, List.forall_mem_cons.2 ⟨subd0_3_26, List.forall_mem_cons.2 ⟨subd0_3_27, List.forall_mem_cons.2 ⟨subd0_3_28, List.forall_mem_cons.2 ⟨subd0_3_29, List.forall_mem_cons.2 ⟨subd0_3_30, List.forall_mem_cons.2 ⟨subd0_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_3_32 : subd0_3 [2, -4] = true := by decide +kernel
theorem subd0_3_33 : subd0_3 [2, -3] = true := by decide +kernel
theorem subd0_3_34 : subd0_3 [2, -2] = true := by decide +kernel
theorem subd0_3_35 : subd0_3 [2, -1] = true := by decide +kernel
theorem subd0_3_36 : subd0_3 [2, 0] = true := by decide +kernel
theorem subd0_3_37 : subd0_3 [2, 1] = true := by decide +kernel
theorem subd0_3_38 : subd0_3 [2, 2] = true := by decide +kernel
theorem subd0_3_39 : subd0_3 [3] = true := by decide +kernel
theorem sbd0_3_1 : ∀ q ∈ blkd0_3_1, subd0_3 q = true := by
  unfold blkd0_3_1
  exact List.forall_mem_cons.2 ⟨subd0_3_32, List.forall_mem_cons.2 ⟨subd0_3_33, List.forall_mem_cons.2 ⟨subd0_3_34, List.forall_mem_cons.2 ⟨subd0_3_35, List.forall_mem_cons.2 ⟨subd0_3_36, List.forall_mem_cons.2 ⟨subd0_3_37, List.forall_mem_cons.2 ⟨subd0_3_38, List.forall_mem_cons.2 ⟨subd0_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_4 : ldCheck G d0_4.U d0_4.ms ldd0_4 = true := by decide +kernel
theorem pre_okd0_4 : subPre G cell0 d0_4 = true := by decide +kernel
theorem subd0_4_0 : subd0_4 [-1] = true := by decide +kernel
theorem subd0_4_1 : subd0_4 [0] = true := by decide +kernel
theorem subd0_4_2 : subd0_4 [1] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_cons.2 ⟨subd0_4_1, List.forall_mem_cons.2 ⟨subd0_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd0_5 : ldCheck G d0_5.U d0_5.ms ldd0_5 = true := by decide +kernel
theorem pre_okd0_5 : subPre G cell0 d0_5 = true := by decide +kernel
theorem subd0_5_0 : subd0_5 [] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_nil _⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [-1] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [0] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [1] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
