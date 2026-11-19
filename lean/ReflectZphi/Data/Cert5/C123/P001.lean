import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_6 : ldCheck G d0_6.U d0_6.ms ldd0_6 = true := by decide +kernel
theorem pre_okd0_6 : subPre G cell0 d0_6 = true := by decide +kernel
theorem subd0_6_0 : subd0_6 [-4] = true := by decide +kernel
theorem subd0_6_1 : subd0_6 [-3, -3] = true := by decide +kernel
theorem subd0_6_2 : subd0_6 [-3, -2] = true := by decide +kernel
theorem subd0_6_3 : subd0_6 [-3, -1] = true := by decide +kernel
theorem subd0_6_4 : subd0_6 [-3, 0] = true := by decide +kernel
theorem subd0_6_5 : subd0_6 [-3, 1] = true := by decide +kernel
theorem subd0_6_6 : subd0_6 [-3, 2] = true := by decide +kernel
theorem subd0_6_7 : subd0_6 [-3, 3] = true := by decide +kernel
theorem subd0_6_8 : subd0_6 [-2, -4] = true := by decide +kernel
theorem subd0_6_9 : subd0_6 [-2, -3] = true := by decide +kernel
theorem subd0_6_10 : subd0_6 [-2, -2] = true := by decide +kernel
theorem subd0_6_11 : subd0_6 [-2, -1] = true := by decide +kernel
theorem subd0_6_12 : subd0_6 [-2, 0] = true := by decide +kernel
theorem subd0_6_13 : subd0_6 [-2, 1] = true := by decide +kernel
theorem subd0_6_14 : subd0_6 [-2, 2] = true := by decide +kernel
theorem subd0_6_15 : subd0_6 [-2, 3] = true := by decide +kernel
theorem subd0_6_16 : subd0_6 [-1, -5] = true := by decide +kernel
theorem subd0_6_17 : subd0_6 [-1, -4] = true := by decide +kernel
theorem subd0_6_18 : subd0_6 [-1, -3] = true := by decide +kernel
theorem subd0_6_19 : subd0_6 [-1, -2] = true := by decide +kernel
theorem subd0_6_20 : subd0_6 [-1, -1] = true := by decide +kernel
theorem subd0_6_21 : subd0_6 [-1, 0] = true := by decide +kernel
theorem subd0_6_22 : subd0_6 [-1, 1] = true := by decide +kernel
theorem subd0_6_23 : subd0_6 [-1, 2] = true := by decide +kernel
theorem subd0_6_24 : subd0_6 [-1, 3] = true := by decide +kernel
theorem subd0_6_25 : subd0_6 [-1, 4] = true := by decide +kernel
theorem subd0_6_26 : subd0_6 [0, -5] = true := by decide +kernel
theorem subd0_6_27 : subd0_6 [0, -4] = true := by decide +kernel
theorem subd0_6_28 : subd0_6 [0, -3] = true := by decide +kernel
theorem subd0_6_29 : subd0_6 [0, -2] = true := by decide +kernel
theorem subd0_6_30 : subd0_6 [0, -1] = true := by decide +kernel
theorem subd0_6_31 : subd0_6 [0, 0] = true := by decide +kernel
theorem sbd0_6_0 : ∀ q ∈ blkd0_6_0, subd0_6 q = true := by
  unfold blkd0_6_0
  exact List.forall_mem_cons.2 ⟨subd0_6_0, List.forall_mem_cons.2 ⟨subd0_6_1, List.forall_mem_cons.2 ⟨subd0_6_2, List.forall_mem_cons.2 ⟨subd0_6_3, List.forall_mem_cons.2 ⟨subd0_6_4, List.forall_mem_cons.2 ⟨subd0_6_5, List.forall_mem_cons.2 ⟨subd0_6_6, List.forall_mem_cons.2 ⟨subd0_6_7, List.forall_mem_cons.2 ⟨subd0_6_8, List.forall_mem_cons.2 ⟨subd0_6_9, List.forall_mem_cons.2 ⟨subd0_6_10, List.forall_mem_cons.2 ⟨subd0_6_11, List.forall_mem_cons.2 ⟨subd0_6_12, List.forall_mem_cons.2 ⟨subd0_6_13, List.forall_mem_cons.2 ⟨subd0_6_14, List.forall_mem_cons.2 ⟨subd0_6_15, List.forall_mem_cons.2 ⟨subd0_6_16, List.forall_mem_cons.2 ⟨subd0_6_17, List.forall_mem_cons.2 ⟨subd0_6_18, List.forall_mem_cons.2 ⟨subd0_6_19, List.forall_mem_cons.2 ⟨subd0_6_20, List.forall_mem_cons.2 ⟨subd0_6_21, List.forall_mem_cons.2 ⟨subd0_6_22, List.forall_mem_cons.2 ⟨subd0_6_23, List.forall_mem_cons.2 ⟨subd0_6_24, List.forall_mem_cons.2 ⟨subd0_6_25, List.forall_mem_cons.2 ⟨subd0_6_26, List.forall_mem_cons.2 ⟨subd0_6_27, List.forall_mem_cons.2 ⟨subd0_6_28, List.forall_mem_cons.2 ⟨subd0_6_29, List.forall_mem_cons.2 ⟨subd0_6_30, List.forall_mem_cons.2 ⟨subd0_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd0_6_32 : subd0_6 [0, 1] = true := by decide +kernel
theorem subd0_6_33 : subd0_6 [0, 2] = true := by decide +kernel
theorem subd0_6_34 : subd0_6 [0, 3] = true := by decide +kernel
theorem subd0_6_35 : subd0_6 [0, 4] = true := by decide +kernel
theorem subd0_6_36 : subd0_6 [1, -5] = true := by decide +kernel
theorem subd0_6_37 : subd0_6 [1, -4] = true := by decide +kernel
theorem subd0_6_38 : subd0_6 [1, -3] = true := by decide +kernel
theorem subd0_6_39 : subd0_6 [1, -2] = true := by decide +kernel
theorem subd0_6_40 : subd0_6 [1, -1] = true := by decide +kernel
theorem subd0_6_41 : subd0_6 [1, 0] = true := by decide +kernel
theorem subd0_6_42 : subd0_6 [1, 1] = true := by decide +kernel
theorem subd0_6_43 : subd0_6 [1, 2] = true := by decide +kernel
theorem subd0_6_44 : subd0_6 [1, 3] = true := by decide +kernel
theorem subd0_6_45 : subd0_6 [1, 4] = true := by decide +kernel
theorem subd0_6_46 : subd0_6 [2, -4] = true := by decide +kernel
theorem subd0_6_47 : subd0_6 [2, -3] = true := by decide +kernel
theorem subd0_6_48 : subd0_6 [2, -2] = true := by decide +kernel
theorem subd0_6_49 : subd0_6 [2, -1] = true := by decide +kernel
theorem subd0_6_50 : subd0_6 [2, 0] = true := by decide +kernel
theorem subd0_6_51 : subd0_6 [2, 1] = true := by decide +kernel
theorem subd0_6_52 : subd0_6 [2, 2] = true := by decide +kernel
theorem subd0_6_53 : subd0_6 [2, 3] = true := by decide +kernel
theorem subd0_6_54 : subd0_6 [3, -4] = true := by decide +kernel
theorem subd0_6_55 : subd0_6 [3, -3] = true := by decide +kernel
theorem subd0_6_56 : subd0_6 [3, -2] = true := by decide +kernel
theorem subd0_6_57 : subd0_6 [3, -1] = true := by decide +kernel
theorem subd0_6_58 : subd0_6 [3, 0] = true := by decide +kernel
theorem subd0_6_59 : subd0_6 [3, 1] = true := by decide +kernel
theorem subd0_6_60 : subd0_6 [3, 2] = true := by decide +kernel
theorem subd0_6_61 : subd0_6 [4] = true := by decide +kernel
theorem sbd0_6_1 : ∀ q ∈ blkd0_6_1, subd0_6 q = true := by
  unfold blkd0_6_1
  exact List.forall_mem_cons.2 ⟨subd0_6_32, List.forall_mem_cons.2 ⟨subd0_6_33, List.forall_mem_cons.2 ⟨subd0_6_34, List.forall_mem_cons.2 ⟨subd0_6_35, List.forall_mem_cons.2 ⟨subd0_6_36, List.forall_mem_cons.2 ⟨subd0_6_37, List.forall_mem_cons.2 ⟨subd0_6_38, List.forall_mem_cons.2 ⟨subd0_6_39, List.forall_mem_cons.2 ⟨subd0_6_40, List.forall_mem_cons.2 ⟨subd0_6_41, List.forall_mem_cons.2 ⟨subd0_6_42, List.forall_mem_cons.2 ⟨subd0_6_43, List.forall_mem_cons.2 ⟨subd0_6_44, List.forall_mem_cons.2 ⟨subd0_6_45, List.forall_mem_cons.2 ⟨subd0_6_46, List.forall_mem_cons.2 ⟨subd0_6_47, List.forall_mem_cons.2 ⟨subd0_6_48, List.forall_mem_cons.2 ⟨subd0_6_49, List.forall_mem_cons.2 ⟨subd0_6_50, List.forall_mem_cons.2 ⟨subd0_6_51, List.forall_mem_cons.2 ⟨subd0_6_52, List.forall_mem_cons.2 ⟨subd0_6_53, List.forall_mem_cons.2 ⟨subd0_6_54, List.forall_mem_cons.2 ⟨subd0_6_55, List.forall_mem_cons.2 ⟨subd0_6_56, List.forall_mem_cons.2 ⟨subd0_6_57, List.forall_mem_cons.2 ⟨subd0_6_58, List.forall_mem_cons.2 ⟨subd0_6_59, List.forall_mem_cons.2 ⟨subd0_6_60, List.forall_mem_cons.2 ⟨subd0_6_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_nil _⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_nil _⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_nil _⟩
theorem ld_okd1_4 : ldCheck G d1_4.U d1_4.ms ldd1_4 = true := by decide +kernel
theorem pre_okd1_4 : subPre G cell1 d1_4 = true := by decide +kernel
theorem subd1_4_0 : subd1_4 [-1] = true := by decide +kernel
theorem subd1_4_1 : subd1_4 [0, -3] = true := by decide +kernel
theorem subd1_4_2 : subd1_4 [0, -2] = true := by decide +kernel
theorem subd1_4_3 : subd1_4 [0, -1] = true := by decide +kernel
theorem subd1_4_4 : subd1_4 [0, 0] = true := by decide +kernel
theorem subd1_4_5 : subd1_4 [0, 1] = true := by decide +kernel
theorem subd1_4_6 : subd1_4 [0, 2] = true := by decide +kernel
theorem subd1_4_7 : subd1_4 [1] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_cons.2 ⟨subd1_4_1, List.forall_mem_cons.2 ⟨subd1_4_2, List.forall_mem_cons.2 ⟨subd1_4_3, List.forall_mem_cons.2 ⟨subd1_4_4, List.forall_mem_cons.2 ⟨subd1_4_5, List.forall_mem_cons.2 ⟨subd1_4_6, List.forall_mem_cons.2 ⟨subd1_4_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
