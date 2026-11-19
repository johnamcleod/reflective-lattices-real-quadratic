import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_10 : ldCheck G d9_10.U d9_10.ms ldd9_10 = true := by decide +kernel
theorem pre_okd9_10 : subPre G cell9 d9_10 = true := by decide +kernel
theorem subd9_10_0 : subd9_10 [-3] = true := by decide +kernel
theorem subd9_10_1 : subd9_10 [-2, -2] = true := by decide +kernel
theorem subd9_10_2 : subd9_10 [-2, -1] = true := by decide +kernel
theorem subd9_10_3 : subd9_10 [-2, 0] = true := by decide +kernel
theorem subd9_10_4 : subd9_10 [-2, 1] = true := by decide +kernel
theorem subd9_10_5 : subd9_10 [-2, 2] = true := by decide +kernel
theorem subd9_10_6 : subd9_10 [-2, 3] = true := by decide +kernel
theorem subd9_10_7 : subd9_10 [-1, -3] = true := by decide +kernel
theorem subd9_10_8 : subd9_10 [-1, -2] = true := by decide +kernel
theorem subd9_10_9 : subd9_10 [-1, -1] = true := by decide +kernel
theorem subd9_10_10 : subd9_10 [-1, 0] = true := by decide +kernel
theorem subd9_10_11 : subd9_10 [-1, 1] = true := by decide +kernel
theorem subd9_10_12 : subd9_10 [-1, 2] = true := by decide +kernel
theorem subd9_10_13 : subd9_10 [-1, 3] = true := by decide +kernel
theorem subd9_10_14 : subd9_10 [0, -4] = true := by decide +kernel
theorem subd9_10_15 : subd9_10 [0, -3] = true := by decide +kernel
theorem subd9_10_16 : subd9_10 [0, -2] = true := by decide +kernel
theorem subd9_10_17 : subd9_10 [0, -1] = true := by decide +kernel
theorem subd9_10_18 : subd9_10 [0, 0] = true := by decide +kernel
theorem subd9_10_19 : subd9_10 [0, 1] = true := by decide +kernel
theorem subd9_10_20 : subd9_10 [0, 2] = true := by decide +kernel
theorem subd9_10_21 : subd9_10 [0, 3] = true := by decide +kernel
theorem subd9_10_22 : subd9_10 [1, -4] = true := by decide +kernel
theorem subd9_10_23 : subd9_10 [1, -3] = true := by decide +kernel
theorem subd9_10_24 : subd9_10 [1, -2] = true := by decide +kernel
theorem subd9_10_25 : subd9_10 [1, -1] = true := by decide +kernel
theorem subd9_10_26 : subd9_10 [1, 0] = true := by decide +kernel
theorem subd9_10_27 : subd9_10 [1, 1] = true := by decide +kernel
theorem subd9_10_28 : subd9_10 [1, 2] = true := by decide +kernel
theorem subd9_10_29 : subd9_10 [2, -4] = true := by decide +kernel
theorem subd9_10_30 : subd9_10 [2, -3] = true := by decide +kernel
theorem subd9_10_31 : subd9_10 [2, -2] = true := by decide +kernel
theorem sbd9_10_0 : ∀ q ∈ blkd9_10_0, subd9_10 q = true := by
  unfold blkd9_10_0
  exact List.forall_mem_cons.2 ⟨subd9_10_0, List.forall_mem_cons.2 ⟨subd9_10_1, List.forall_mem_cons.2 ⟨subd9_10_2, List.forall_mem_cons.2 ⟨subd9_10_3, List.forall_mem_cons.2 ⟨subd9_10_4, List.forall_mem_cons.2 ⟨subd9_10_5, List.forall_mem_cons.2 ⟨subd9_10_6, List.forall_mem_cons.2 ⟨subd9_10_7, List.forall_mem_cons.2 ⟨subd9_10_8, List.forall_mem_cons.2 ⟨subd9_10_9, List.forall_mem_cons.2 ⟨subd9_10_10, List.forall_mem_cons.2 ⟨subd9_10_11, List.forall_mem_cons.2 ⟨subd9_10_12, List.forall_mem_cons.2 ⟨subd9_10_13, List.forall_mem_cons.2 ⟨subd9_10_14, List.forall_mem_cons.2 ⟨subd9_10_15, List.forall_mem_cons.2 ⟨subd9_10_16, List.forall_mem_cons.2 ⟨subd9_10_17, List.forall_mem_cons.2 ⟨subd9_10_18, List.forall_mem_cons.2 ⟨subd9_10_19, List.forall_mem_cons.2 ⟨subd9_10_20, List.forall_mem_cons.2 ⟨subd9_10_21, List.forall_mem_cons.2 ⟨subd9_10_22, List.forall_mem_cons.2 ⟨subd9_10_23, List.forall_mem_cons.2 ⟨subd9_10_24, List.forall_mem_cons.2 ⟨subd9_10_25, List.forall_mem_cons.2 ⟨subd9_10_26, List.forall_mem_cons.2 ⟨subd9_10_27, List.forall_mem_cons.2 ⟨subd9_10_28, List.forall_mem_cons.2 ⟨subd9_10_29, List.forall_mem_cons.2 ⟨subd9_10_30, List.forall_mem_cons.2 ⟨subd9_10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_10_32 : subd9_10 [2, -1] = true := by decide +kernel
theorem subd9_10_33 : subd9_10 [2, 0] = true := by decide +kernel
theorem subd9_10_34 : subd9_10 [2, 1] = true := by decide +kernel
theorem subd9_10_35 : subd9_10 [3] = true := by decide +kernel
theorem sbd9_10_1 : ∀ q ∈ blkd9_10_1, subd9_10 q = true := by
  unfold blkd9_10_1
  exact List.forall_mem_cons.2 ⟨subd9_10_32, List.forall_mem_cons.2 ⟨subd9_10_33, List.forall_mem_cons.2 ⟨subd9_10_34, List.forall_mem_cons.2 ⟨subd9_10_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd9_11 : ldCheck G d9_11.U d9_11.ms ldd9_11 = true := by decide +kernel
theorem pre_okd9_11 : subPre G cell9 d9_11 = true := by decide +kernel
theorem subd9_11_0 : subd9_11 [-4] = true := by decide +kernel
theorem subd9_11_1 : subd9_11 [-3, -3] = true := by decide +kernel
theorem subd9_11_2 : subd9_11 [-3, -2] = true := by decide +kernel
theorem subd9_11_3 : subd9_11 [-3, -1] = true := by decide +kernel
theorem subd9_11_4 : subd9_11 [-3, 0] = true := by decide +kernel
theorem subd9_11_5 : subd9_11 [-3, 1] = true := by decide +kernel
theorem subd9_11_6 : subd9_11 [-3, 2] = true := by decide +kernel
theorem subd9_11_7 : subd9_11 [-3, 3] = true := by decide +kernel
theorem subd9_11_8 : subd9_11 [-2, -4] = true := by decide +kernel
theorem subd9_11_9 : subd9_11 [-2, -3] = true := by decide +kernel
theorem subd9_11_10 : subd9_11 [-2, -2] = true := by decide +kernel
theorem subd9_11_11 : subd9_11 [-2, -1] = true := by decide +kernel
theorem subd9_11_12 : subd9_11 [-2, 0] = true := by decide +kernel
theorem subd9_11_13 : subd9_11 [-2, 1] = true := by decide +kernel
theorem subd9_11_14 : subd9_11 [-2, 2] = true := by decide +kernel
theorem subd9_11_15 : subd9_11 [-2, 3] = true := by decide +kernel
theorem subd9_11_16 : subd9_11 [-2, 4] = true := by decide +kernel
theorem subd9_11_17 : subd9_11 [-1, -4] = true := by decide +kernel
theorem subd9_11_18 : subd9_11 [-1, -3] = true := by decide +kernel
theorem subd9_11_19 : subd9_11 [-1, -2] = true := by decide +kernel
theorem subd9_11_20 : subd9_11 [-1, -1] = true := by decide +kernel
theorem subd9_11_21 : subd9_11 [-1, 0] = true := by decide +kernel
theorem subd9_11_22 : subd9_11 [-1, 1] = true := by decide +kernel
theorem subd9_11_23 : subd9_11 [-1, 2] = true := by decide +kernel
theorem subd9_11_24 : subd9_11 [-1, 3] = true := by decide +kernel
theorem subd9_11_25 : subd9_11 [-1, 4] = true := by decide +kernel
theorem subd9_11_26 : subd9_11 [0, -5] = true := by decide +kernel
theorem subd9_11_27 : subd9_11 [0, -4] = true := by decide +kernel
theorem subd9_11_28 : subd9_11 [0, -3] = true := by decide +kernel
theorem subd9_11_29 : subd9_11 [0, -2] = true := by decide +kernel
theorem subd9_11_30 : subd9_11 [0, -1] = true := by decide +kernel
theorem subd9_11_31 : subd9_11 [0, 0] = true := by decide +kernel
theorem sbd9_11_0 : ∀ q ∈ blkd9_11_0, subd9_11 q = true := by
  unfold blkd9_11_0
  exact List.forall_mem_cons.2 ⟨subd9_11_0, List.forall_mem_cons.2 ⟨subd9_11_1, List.forall_mem_cons.2 ⟨subd9_11_2, List.forall_mem_cons.2 ⟨subd9_11_3, List.forall_mem_cons.2 ⟨subd9_11_4, List.forall_mem_cons.2 ⟨subd9_11_5, List.forall_mem_cons.2 ⟨subd9_11_6, List.forall_mem_cons.2 ⟨subd9_11_7, List.forall_mem_cons.2 ⟨subd9_11_8, List.forall_mem_cons.2 ⟨subd9_11_9, List.forall_mem_cons.2 ⟨subd9_11_10, List.forall_mem_cons.2 ⟨subd9_11_11, List.forall_mem_cons.2 ⟨subd9_11_12, List.forall_mem_cons.2 ⟨subd9_11_13, List.forall_mem_cons.2 ⟨subd9_11_14, List.forall_mem_cons.2 ⟨subd9_11_15, List.forall_mem_cons.2 ⟨subd9_11_16, List.forall_mem_cons.2 ⟨subd9_11_17, List.forall_mem_cons.2 ⟨subd9_11_18, List.forall_mem_cons.2 ⟨subd9_11_19, List.forall_mem_cons.2 ⟨subd9_11_20, List.forall_mem_cons.2 ⟨subd9_11_21, List.forall_mem_cons.2 ⟨subd9_11_22, List.forall_mem_cons.2 ⟨subd9_11_23, List.forall_mem_cons.2 ⟨subd9_11_24, List.forall_mem_cons.2 ⟨subd9_11_25, List.forall_mem_cons.2 ⟨subd9_11_26, List.forall_mem_cons.2 ⟨subd9_11_27, List.forall_mem_cons.2 ⟨subd9_11_28, List.forall_mem_cons.2 ⟨subd9_11_29, List.forall_mem_cons.2 ⟨subd9_11_30, List.forall_mem_cons.2 ⟨subd9_11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_11_32 : subd9_11 [0, 1] = true := by decide +kernel
theorem subd9_11_33 : subd9_11 [0, 2] = true := by decide +kernel
theorem subd9_11_34 : subd9_11 [0, 3] = true := by decide +kernel
theorem subd9_11_35 : subd9_11 [0, 4] = true := by decide +kernel
theorem subd9_11_36 : subd9_11 [1, -5] = true := by decide +kernel
theorem subd9_11_37 : subd9_11 [1, -4] = true := by decide +kernel
theorem subd9_11_38 : subd9_11 [1, -3] = true := by decide +kernel
theorem subd9_11_39 : subd9_11 [1, -2] = true := by decide +kernel
theorem subd9_11_40 : subd9_11 [1, -1] = true := by decide +kernel
theorem subd9_11_41 : subd9_11 [1, 0] = true := by decide +kernel
theorem subd9_11_42 : subd9_11 [1, 1] = true := by decide +kernel
theorem subd9_11_43 : subd9_11 [1, 2] = true := by decide +kernel
theorem subd9_11_44 : subd9_11 [1, 3] = true := by decide +kernel
theorem subd9_11_45 : subd9_11 [2, -5] = true := by decide +kernel
theorem subd9_11_46 : subd9_11 [2, -4] = true := by decide +kernel
theorem subd9_11_47 : subd9_11 [2, -3] = true := by decide +kernel
theorem subd9_11_48 : subd9_11 [2, -2] = true := by decide +kernel
theorem subd9_11_49 : subd9_11 [2, -1] = true := by decide +kernel
theorem subd9_11_50 : subd9_11 [2, 0] = true := by decide +kernel
theorem subd9_11_51 : subd9_11 [2, 1] = true := by decide +kernel
theorem subd9_11_52 : subd9_11 [2, 2] = true := by decide +kernel
theorem subd9_11_53 : subd9_11 [2, 3] = true := by decide +kernel
theorem subd9_11_54 : subd9_11 [3, -4] = true := by decide +kernel
theorem subd9_11_55 : subd9_11 [3, -3] = true := by decide +kernel
theorem subd9_11_56 : subd9_11 [3, -2] = true := by decide +kernel
theorem subd9_11_57 : subd9_11 [3, -1] = true := by decide +kernel
theorem subd9_11_58 : subd9_11 [3, 0] = true := by decide +kernel
theorem subd9_11_59 : subd9_11 [3, 1] = true := by decide +kernel
theorem subd9_11_60 : subd9_11 [3, 2] = true := by decide +kernel
theorem subd9_11_61 : subd9_11 [4] = true := by decide +kernel
theorem sbd9_11_1 : ∀ q ∈ blkd9_11_1, subd9_11 q = true := by
  unfold blkd9_11_1
  exact List.forall_mem_cons.2 ⟨subd9_11_32, List.forall_mem_cons.2 ⟨subd9_11_33, List.forall_mem_cons.2 ⟨subd9_11_34, List.forall_mem_cons.2 ⟨subd9_11_35, List.forall_mem_cons.2 ⟨subd9_11_36, List.forall_mem_cons.2 ⟨subd9_11_37, List.forall_mem_cons.2 ⟨subd9_11_38, List.forall_mem_cons.2 ⟨subd9_11_39, List.forall_mem_cons.2 ⟨subd9_11_40, List.forall_mem_cons.2 ⟨subd9_11_41, List.forall_mem_cons.2 ⟨subd9_11_42, List.forall_mem_cons.2 ⟨subd9_11_43, List.forall_mem_cons.2 ⟨subd9_11_44, List.forall_mem_cons.2 ⟨subd9_11_45, List.forall_mem_cons.2 ⟨subd9_11_46, List.forall_mem_cons.2 ⟨subd9_11_47, List.forall_mem_cons.2 ⟨subd9_11_48, List.forall_mem_cons.2 ⟨subd9_11_49, List.forall_mem_cons.2 ⟨subd9_11_50, List.forall_mem_cons.2 ⟨subd9_11_51, List.forall_mem_cons.2 ⟨subd9_11_52, List.forall_mem_cons.2 ⟨subd9_11_53, List.forall_mem_cons.2 ⟨subd9_11_54, List.forall_mem_cons.2 ⟨subd9_11_55, List.forall_mem_cons.2 ⟨subd9_11_56, List.forall_mem_cons.2 ⟨subd9_11_57, List.forall_mem_cons.2 ⟨subd9_11_58, List.forall_mem_cons.2 ⟨subd9_11_59, List.forall_mem_cons.2 ⟨subd9_11_60, List.forall_mem_cons.2 ⟨subd9_11_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_12 : ldCheck G d9_12.U d9_12.ms ldd9_12 = true := by decide +kernel
theorem pre_okd9_12 : subPre G cell9 d9_12 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
