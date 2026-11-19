import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_0 : subd11_1 [-4] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-3, -2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-3, -1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-3, 0] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-3, 1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-3, 2] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-3, 3] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-3, 4] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-2, 3] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-2, 4] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-1, 4] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [0, -5] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [0, 1] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [0, 4] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [1, -5] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [2, -5] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [2, -4] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [2, 2] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [3, -5] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [3, -4] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [3, -3] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [3, -2] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [3, -1] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [3, 0] = true := by decide +kernel
theorem subd11_1_58 : subd11_1 [3, 1] = true := by decide +kernel
theorem subd11_1_59 : subd11_1 [4] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_cons.2 ⟨subd11_1_58, List.forall_mem_cons.2 ⟨subd11_1_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-3] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-2, -4] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, 1] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [1, 2] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [1, 3] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [2, 3] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [3] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
