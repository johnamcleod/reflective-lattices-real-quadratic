import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_5_0 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-1, -2] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [-1, -1] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [-1, 0] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [-1, 1] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [-1, 2] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [0, -3] = true := by decide +kernel
theorem subd9_5_7 : subd9_5 [0, -2] = true := by decide +kernel
theorem subd9_5_8 : subd9_5 [0, -1] = true := by decide +kernel
theorem subd9_5_9 : subd9_5 [0, 0] = true := by decide +kernel
theorem subd9_5_10 : subd9_5 [0, 1] = true := by decide +kernel
theorem subd9_5_11 : subd9_5 [0, 2] = true := by decide +kernel
theorem subd9_5_12 : subd9_5 [1, -3] = true := by decide +kernel
theorem subd9_5_13 : subd9_5 [1, -2] = true := by decide +kernel
theorem subd9_5_14 : subd9_5 [1, -1] = true := by decide +kernel
theorem subd9_5_15 : subd9_5 [1, 0] = true := by decide +kernel
theorem subd9_5_16 : subd9_5 [1, 1] = true := by decide +kernel
theorem subd9_5_17 : subd9_5 [2] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_cons.2 ⟨subd9_5_7, List.forall_mem_cons.2 ⟨subd9_5_8, List.forall_mem_cons.2 ⟨subd9_5_9, List.forall_mem_cons.2 ⟨subd9_5_10, List.forall_mem_cons.2 ⟨subd9_5_11, List.forall_mem_cons.2 ⟨subd9_5_12, List.forall_mem_cons.2 ⟨subd9_5_13, List.forall_mem_cons.2 ⟨subd9_5_14, List.forall_mem_cons.2 ⟨subd9_5_15, List.forall_mem_cons.2 ⟨subd9_5_16, List.forall_mem_cons.2 ⟨subd9_5_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [-4] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-3, -4] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-3, -3] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-3, -2] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-3, -1] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-3, 0] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [-3, 1] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [-3, 2] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [-2, -5] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [-2, -4] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [-2, -3] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [-2, -2] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [-2, -1] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [-2, 0] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [-2, 1] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [-2, 2] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [-2, 3] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [-1, -5] = true := by decide +kernel
theorem subd9_6_18 : subd9_6 [-1, -4] = true := by decide +kernel
theorem subd9_6_19 : subd9_6 [-1, -3] = true := by decide +kernel
theorem subd9_6_20 : subd9_6 [-1, -2] = true := by decide +kernel
theorem subd9_6_21 : subd9_6 [-1, -1] = true := by decide +kernel
theorem subd9_6_22 : subd9_6 [-1, 0] = true := by decide +kernel
theorem subd9_6_23 : subd9_6 [-1, 1] = true := by decide +kernel
theorem subd9_6_24 : subd9_6 [-1, 2] = true := by decide +kernel
theorem subd9_6_25 : subd9_6 [-1, 3] = true := by decide +kernel
theorem subd9_6_26 : subd9_6 [-1, 4] = true := by decide +kernel
theorem subd9_6_27 : subd9_6 [0, -5] = true := by decide +kernel
theorem subd9_6_28 : subd9_6 [0, -4] = true := by decide +kernel
theorem subd9_6_29 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_30 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_31 : subd9_6 [0, -1] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_cons.2 ⟨subd9_6_18, List.forall_mem_cons.2 ⟨subd9_6_19, List.forall_mem_cons.2 ⟨subd9_6_20, List.forall_mem_cons.2 ⟨subd9_6_21, List.forall_mem_cons.2 ⟨subd9_6_22, List.forall_mem_cons.2 ⟨subd9_6_23, List.forall_mem_cons.2 ⟨subd9_6_24, List.forall_mem_cons.2 ⟨subd9_6_25, List.forall_mem_cons.2 ⟨subd9_6_26, List.forall_mem_cons.2 ⟨subd9_6_27, List.forall_mem_cons.2 ⟨subd9_6_28, List.forall_mem_cons.2 ⟨subd9_6_29, List.forall_mem_cons.2 ⟨subd9_6_30, List.forall_mem_cons.2 ⟨subd9_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_32 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_33 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_34 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_35 : subd9_6 [0, 3] = true := by decide +kernel
theorem subd9_6_36 : subd9_6 [0, 4] = true := by decide +kernel
theorem subd9_6_37 : subd9_6 [1, -5] = true := by decide +kernel
theorem subd9_6_38 : subd9_6 [1, -4] = true := by decide +kernel
theorem subd9_6_39 : subd9_6 [1, -3] = true := by decide +kernel
theorem subd9_6_40 : subd9_6 [1, -2] = true := by decide +kernel
theorem subd9_6_41 : subd9_6 [1, -1] = true := by decide +kernel
theorem subd9_6_42 : subd9_6 [1, 0] = true := by decide +kernel
theorem subd9_6_43 : subd9_6 [1, 1] = true := by decide +kernel
theorem subd9_6_44 : subd9_6 [1, 2] = true := by decide +kernel
theorem subd9_6_45 : subd9_6 [1, 3] = true := by decide +kernel
theorem subd9_6_46 : subd9_6 [1, 4] = true := by decide +kernel
theorem subd9_6_47 : subd9_6 [2, -4] = true := by decide +kernel
theorem subd9_6_48 : subd9_6 [2, -3] = true := by decide +kernel
theorem subd9_6_49 : subd9_6 [2, -2] = true := by decide +kernel
theorem subd9_6_50 : subd9_6 [2, -1] = true := by decide +kernel
theorem subd9_6_51 : subd9_6 [2, 0] = true := by decide +kernel
theorem subd9_6_52 : subd9_6 [2, 1] = true := by decide +kernel
theorem subd9_6_53 : subd9_6 [2, 2] = true := by decide +kernel
theorem subd9_6_54 : subd9_6 [2, 3] = true := by decide +kernel
theorem subd9_6_55 : subd9_6 [2, 4] = true := by decide +kernel
theorem subd9_6_56 : subd9_6 [3, -3] = true := by decide +kernel
theorem subd9_6_57 : subd9_6 [3, -2] = true := by decide +kernel
theorem subd9_6_58 : subd9_6 [3, -1] = true := by decide +kernel
theorem subd9_6_59 : subd9_6 [3, 0] = true := by decide +kernel
theorem subd9_6_60 : subd9_6 [3, 1] = true := by decide +kernel
theorem subd9_6_61 : subd9_6 [3, 2] = true := by decide +kernel
theorem subd9_6_62 : subd9_6 [3, 3] = true := by decide +kernel
theorem subd9_6_63 : subd9_6 [4] = true := by decide +kernel
theorem sbd9_6_1 : ∀ q ∈ blkd9_6_1, subd9_6 q = true := by
  unfold blkd9_6_1
  exact List.forall_mem_cons.2 ⟨subd9_6_32, List.forall_mem_cons.2 ⟨subd9_6_33, List.forall_mem_cons.2 ⟨subd9_6_34, List.forall_mem_cons.2 ⟨subd9_6_35, List.forall_mem_cons.2 ⟨subd9_6_36, List.forall_mem_cons.2 ⟨subd9_6_37, List.forall_mem_cons.2 ⟨subd9_6_38, List.forall_mem_cons.2 ⟨subd9_6_39, List.forall_mem_cons.2 ⟨subd9_6_40, List.forall_mem_cons.2 ⟨subd9_6_41, List.forall_mem_cons.2 ⟨subd9_6_42, List.forall_mem_cons.2 ⟨subd9_6_43, List.forall_mem_cons.2 ⟨subd9_6_44, List.forall_mem_cons.2 ⟨subd9_6_45, List.forall_mem_cons.2 ⟨subd9_6_46, List.forall_mem_cons.2 ⟨subd9_6_47, List.forall_mem_cons.2 ⟨subd9_6_48, List.forall_mem_cons.2 ⟨subd9_6_49, List.forall_mem_cons.2 ⟨subd9_6_50, List.forall_mem_cons.2 ⟨subd9_6_51, List.forall_mem_cons.2 ⟨subd9_6_52, List.forall_mem_cons.2 ⟨subd9_6_53, List.forall_mem_cons.2 ⟨subd9_6_54, List.forall_mem_cons.2 ⟨subd9_6_55, List.forall_mem_cons.2 ⟨subd9_6_56, List.forall_mem_cons.2 ⟨subd9_6_57, List.forall_mem_cons.2 ⟨subd9_6_58, List.forall_mem_cons.2 ⟨subd9_6_59, List.forall_mem_cons.2 ⟨subd9_6_60, List.forall_mem_cons.2 ⟨subd9_6_61, List.forall_mem_cons.2 ⟨subd9_6_62, List.forall_mem_cons.2 ⟨subd9_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [0] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [1] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
