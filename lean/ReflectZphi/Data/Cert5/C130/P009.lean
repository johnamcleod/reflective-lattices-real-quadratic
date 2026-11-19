import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-3] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-2, 4] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-1, 4] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [0, -5] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [1, -2] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [2, -5] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [2, -2] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [2, -1] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [2, 2] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [3] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-3] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-2, -3] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-2, -2] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-2, -1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-2, 0] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-2, 1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-2, 2] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [-2, 3] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [-1, -4] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [-1, 3] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [-1, 4] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [0, -5] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_20 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_21 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_22 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_23 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_24 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_25 : subd10_0 [0, 3] = true := by decide +kernel
theorem subd10_0_26 : subd10_0 [0, 4] = true := by decide +kernel
theorem subd10_0_27 : subd10_0 [1, -5] = true := by decide +kernel
theorem subd10_0_28 : subd10_0 [1, -4] = true := by decide +kernel
theorem subd10_0_29 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_30 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_31 : subd10_0 [1, -1] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_cons.2 ⟨subd10_0_20, List.forall_mem_cons.2 ⟨subd10_0_21, List.forall_mem_cons.2 ⟨subd10_0_22, List.forall_mem_cons.2 ⟨subd10_0_23, List.forall_mem_cons.2 ⟨subd10_0_24, List.forall_mem_cons.2 ⟨subd10_0_25, List.forall_mem_cons.2 ⟨subd10_0_26, List.forall_mem_cons.2 ⟨subd10_0_27, List.forall_mem_cons.2 ⟨subd10_0_28, List.forall_mem_cons.2 ⟨subd10_0_29, List.forall_mem_cons.2 ⟨subd10_0_30, List.forall_mem_cons.2 ⟨subd10_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_32 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_33 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_34 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_35 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_36 : subd10_0 [2, -4] = true := by decide +kernel
theorem subd10_0_37 : subd10_0 [2, -3] = true := by decide +kernel
theorem subd10_0_38 : subd10_0 [2, -2] = true := by decide +kernel
theorem subd10_0_39 : subd10_0 [2, -1] = true := by decide +kernel
theorem subd10_0_40 : subd10_0 [2, 0] = true := by decide +kernel
theorem subd10_0_41 : subd10_0 [2, 1] = true := by decide +kernel
theorem subd10_0_42 : subd10_0 [2, 2] = true := by decide +kernel
theorem subd10_0_43 : subd10_0 [3] = true := by decide +kernel
theorem sbd10_0_1 : ∀ q ∈ blkd10_0_1, subd10_0 q = true := by
  unfold blkd10_0_1
  exact List.forall_mem_cons.2 ⟨subd10_0_32, List.forall_mem_cons.2 ⟨subd10_0_33, List.forall_mem_cons.2 ⟨subd10_0_34, List.forall_mem_cons.2 ⟨subd10_0_35, List.forall_mem_cons.2 ⟨subd10_0_36, List.forall_mem_cons.2 ⟨subd10_0_37, List.forall_mem_cons.2 ⟨subd10_0_38, List.forall_mem_cons.2 ⟨subd10_0_39, List.forall_mem_cons.2 ⟨subd10_0_40, List.forall_mem_cons.2 ⟨subd10_0_41, List.forall_mem_cons.2 ⟨subd10_0_42, List.forall_mem_cons.2 ⟨subd10_0_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-4] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-3, -4] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-3, -3] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-3, -2] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-3, -1] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-3, 0] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-3, 1] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-3, 2] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-2, -5] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-2, -4] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-2, -2] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-2, 0] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-2, 1] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-2, 2] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-2, 3] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [-1, -5] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [0, -5] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [0, 0] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C130
