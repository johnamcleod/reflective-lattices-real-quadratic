import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_32 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [2, -4] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [2, -1] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [2, 0] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [3] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [4] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-3, -2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-3, -1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-3, 0] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-3, 1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-3, 2] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-3, 3] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-2, -1] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-2, 0] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-2, 1] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-2, 2] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-2, 4] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-1, -4] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-1, 3] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-1, 4] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [0, -5] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [0, 2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [0, 3] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [0, 4] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [1, -5] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [1, -4] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [1, 3] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [2, -5] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [2, -4] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [2, -3] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [2, -2] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [2, -1] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [2, 0] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [2, 1] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [3, -5] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [3, -4] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [3, -3] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [3, -2] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [3, -1] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [3, 0] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [3, 1] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-3] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-2, -1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-2, 0] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-2, 1] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-2, 2] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [2, -3] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [2, 0] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [3] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
