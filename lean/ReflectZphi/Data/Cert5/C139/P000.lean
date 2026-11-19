import ReflectZphi.Data.Cert5.C139.Base

namespace ReflectZphi.Data.Cert5.C139

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
theorem subd0_1_0 : subd0_1 [-2] = true := by decide +kernel
theorem subd0_1_1 : subd0_1 [-1] = true := by decide +kernel
theorem subd0_1_2 : subd0_1 [0, -4] = true := by decide +kernel
theorem subd0_1_3 : subd0_1 [0, -3] = true := by decide +kernel
theorem subd0_1_4 : subd0_1 [0, -2] = true := by decide +kernel
theorem subd0_1_5 : subd0_1 [0, -1] = true := by decide +kernel
theorem subd0_1_6 : subd0_1 [0, 0] = true := by decide +kernel
theorem subd0_1_7 : subd0_1 [0, 1] = true := by decide +kernel
theorem subd0_1_8 : subd0_1 [0, 2] = true := by decide +kernel
theorem subd0_1_9 : subd0_1 [0, 3] = true := by decide +kernel
theorem subd0_1_10 : subd0_1 [1] = true := by decide +kernel
theorem subd0_1_11 : subd0_1 [2] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_cons.2 ⟨subd0_1_1, List.forall_mem_cons.2 ⟨subd0_1_2, List.forall_mem_cons.2 ⟨subd0_1_3, List.forall_mem_cons.2 ⟨subd0_1_4, List.forall_mem_cons.2 ⟨subd0_1_5, List.forall_mem_cons.2 ⟨subd0_1_6, List.forall_mem_cons.2 ⟨subd0_1_7, List.forall_mem_cons.2 ⟨subd0_1_8, List.forall_mem_cons.2 ⟨subd0_1_9, List.forall_mem_cons.2 ⟨subd0_1_10, List.forall_mem_cons.2 ⟨subd0_1_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_2 : ldCheck G d0_2.U d0_2.ms ldd0_2 = true := by decide +kernel
theorem pre_okd0_2 : subPre G cell0 d0_2 = true := by decide +kernel
theorem subd0_2_0 : subd0_2 [] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_nil _⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [-1] = true := by decide +kernel
theorem subd0_3_1 : subd0_3 [0] = true := by decide +kernel
theorem subd0_3_2 : subd0_3 [1] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_cons.2 ⟨subd0_3_1, List.forall_mem_cons.2 ⟨subd0_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [-3] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [-2, -3] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [-2, -2] = true := by decide +kernel
theorem subd1_1_3 : subd1_1 [-2, -1] = true := by decide +kernel
theorem subd1_1_4 : subd1_1 [-2, 0] = true := by decide +kernel
theorem subd1_1_5 : subd1_1 [-2, 1] = true := by decide +kernel
theorem subd1_1_6 : subd1_1 [-2, 2] = true := by decide +kernel
theorem subd1_1_7 : subd1_1 [-2, 3] = true := by decide +kernel
theorem subd1_1_8 : subd1_1 [-1, -4] = true := by decide +kernel
theorem subd1_1_9 : subd1_1 [-1, -3] = true := by decide +kernel
theorem subd1_1_10 : subd1_1 [-1, -2] = true := by decide +kernel
theorem subd1_1_11 : subd1_1 [-1, -1] = true := by decide +kernel
theorem subd1_1_12 : subd1_1 [-1, 0] = true := by decide +kernel
theorem subd1_1_13 : subd1_1 [-1, 1] = true := by decide +kernel
theorem subd1_1_14 : subd1_1 [-1, 2] = true := by decide +kernel
theorem subd1_1_15 : subd1_1 [-1, 3] = true := by decide +kernel
theorem subd1_1_16 : subd1_1 [0, -4] = true := by decide +kernel
theorem subd1_1_17 : subd1_1 [0, -3] = true := by decide +kernel
theorem subd1_1_18 : subd1_1 [0, -2] = true := by decide +kernel
theorem subd1_1_19 : subd1_1 [0, -1] = true := by decide +kernel
theorem subd1_1_20 : subd1_1 [0, 0] = true := by decide +kernel
theorem subd1_1_21 : subd1_1 [0, 1] = true := by decide +kernel
theorem subd1_1_22 : subd1_1 [0, 2] = true := by decide +kernel
theorem subd1_1_23 : subd1_1 [0, 3] = true := by decide +kernel
theorem subd1_1_24 : subd1_1 [1, -4] = true := by decide +kernel
theorem subd1_1_25 : subd1_1 [1, -3] = true := by decide +kernel
theorem subd1_1_26 : subd1_1 [1, -2] = true := by decide +kernel
theorem subd1_1_27 : subd1_1 [1, -1] = true := by decide +kernel
theorem subd1_1_28 : subd1_1 [1, 0] = true := by decide +kernel
theorem subd1_1_29 : subd1_1 [1, 1] = true := by decide +kernel
theorem subd1_1_30 : subd1_1 [1, 2] = true := by decide +kernel
theorem subd1_1_31 : subd1_1 [1, 3] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_cons.2 ⟨subd1_1_3, List.forall_mem_cons.2 ⟨subd1_1_4, List.forall_mem_cons.2 ⟨subd1_1_5, List.forall_mem_cons.2 ⟨subd1_1_6, List.forall_mem_cons.2 ⟨subd1_1_7, List.forall_mem_cons.2 ⟨subd1_1_8, List.forall_mem_cons.2 ⟨subd1_1_9, List.forall_mem_cons.2 ⟨subd1_1_10, List.forall_mem_cons.2 ⟨subd1_1_11, List.forall_mem_cons.2 ⟨subd1_1_12, List.forall_mem_cons.2 ⟨subd1_1_13, List.forall_mem_cons.2 ⟨subd1_1_14, List.forall_mem_cons.2 ⟨subd1_1_15, List.forall_mem_cons.2 ⟨subd1_1_16, List.forall_mem_cons.2 ⟨subd1_1_17, List.forall_mem_cons.2 ⟨subd1_1_18, List.forall_mem_cons.2 ⟨subd1_1_19, List.forall_mem_cons.2 ⟨subd1_1_20, List.forall_mem_cons.2 ⟨subd1_1_21, List.forall_mem_cons.2 ⟨subd1_1_22, List.forall_mem_cons.2 ⟨subd1_1_23, List.forall_mem_cons.2 ⟨subd1_1_24, List.forall_mem_cons.2 ⟨subd1_1_25, List.forall_mem_cons.2 ⟨subd1_1_26, List.forall_mem_cons.2 ⟨subd1_1_27, List.forall_mem_cons.2 ⟨subd1_1_28, List.forall_mem_cons.2 ⟨subd1_1_29, List.forall_mem_cons.2 ⟨subd1_1_30, List.forall_mem_cons.2 ⟨subd1_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_1_32 : subd1_1 [2, -4] = true := by decide +kernel
theorem subd1_1_33 : subd1_1 [2, -3] = true := by decide +kernel
theorem subd1_1_34 : subd1_1 [2, -2] = true := by decide +kernel
theorem subd1_1_35 : subd1_1 [2, -1] = true := by decide +kernel
theorem subd1_1_36 : subd1_1 [2, 0] = true := by decide +kernel
theorem subd1_1_37 : subd1_1 [2, 1] = true := by decide +kernel
theorem subd1_1_38 : subd1_1 [2, 2] = true := by decide +kernel
theorem subd1_1_39 : subd1_1 [3] = true := by decide +kernel
theorem sbd1_1_1 : ∀ q ∈ blkd1_1_1, subd1_1 q = true := by
  unfold blkd1_1_1
  exact List.forall_mem_cons.2 ⟨subd1_1_32, List.forall_mem_cons.2 ⟨subd1_1_33, List.forall_mem_cons.2 ⟨subd1_1_34, List.forall_mem_cons.2 ⟨subd1_1_35, List.forall_mem_cons.2 ⟨subd1_1_36, List.forall_mem_cons.2 ⟨subd1_1_37, List.forall_mem_cons.2 ⟨subd1_1_38, List.forall_mem_cons.2 ⟨subd1_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C139
