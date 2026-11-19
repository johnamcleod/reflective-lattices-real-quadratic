import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_12_0 : subd9_12 [-2] = true := by decide +kernel
theorem subd9_12_1 : subd9_12 [-1, -3] = true := by decide +kernel
theorem subd9_12_2 : subd9_12 [-1, -2] = true := by decide +kernel
theorem subd9_12_3 : subd9_12 [-1, -1] = true := by decide +kernel
theorem subd9_12_4 : subd9_12 [-1, 0] = true := by decide +kernel
theorem subd9_12_5 : subd9_12 [-1, 1] = true := by decide +kernel
theorem subd9_12_6 : subd9_12 [-1, 2] = true := by decide +kernel
theorem subd9_12_7 : subd9_12 [-1, 3] = true := by decide +kernel
theorem subd9_12_8 : subd9_12 [0, -4] = true := by decide +kernel
theorem subd9_12_9 : subd9_12 [0, -3] = true := by decide +kernel
theorem subd9_12_10 : subd9_12 [0, -2] = true := by decide +kernel
theorem subd9_12_11 : subd9_12 [0, -1] = true := by decide +kernel
theorem subd9_12_12 : subd9_12 [0, 0] = true := by decide +kernel
theorem subd9_12_13 : subd9_12 [0, 1] = true := by decide +kernel
theorem subd9_12_14 : subd9_12 [0, 2] = true := by decide +kernel
theorem subd9_12_15 : subd9_12 [0, 3] = true := by decide +kernel
theorem subd9_12_16 : subd9_12 [1, -4] = true := by decide +kernel
theorem subd9_12_17 : subd9_12 [1, -3] = true := by decide +kernel
theorem subd9_12_18 : subd9_12 [1, -2] = true := by decide +kernel
theorem subd9_12_19 : subd9_12 [1, -1] = true := by decide +kernel
theorem subd9_12_20 : subd9_12 [1, 0] = true := by decide +kernel
theorem subd9_12_21 : subd9_12 [1, 1] = true := by decide +kernel
theorem subd9_12_22 : subd9_12 [1, 2] = true := by decide +kernel
theorem subd9_12_23 : subd9_12 [2] = true := by decide +kernel
theorem sbd9_12_0 : ∀ q ∈ blkd9_12_0, subd9_12 q = true := by
  unfold blkd9_12_0
  exact List.forall_mem_cons.2 ⟨subd9_12_0, List.forall_mem_cons.2 ⟨subd9_12_1, List.forall_mem_cons.2 ⟨subd9_12_2, List.forall_mem_cons.2 ⟨subd9_12_3, List.forall_mem_cons.2 ⟨subd9_12_4, List.forall_mem_cons.2 ⟨subd9_12_5, List.forall_mem_cons.2 ⟨subd9_12_6, List.forall_mem_cons.2 ⟨subd9_12_7, List.forall_mem_cons.2 ⟨subd9_12_8, List.forall_mem_cons.2 ⟨subd9_12_9, List.forall_mem_cons.2 ⟨subd9_12_10, List.forall_mem_cons.2 ⟨subd9_12_11, List.forall_mem_cons.2 ⟨subd9_12_12, List.forall_mem_cons.2 ⟨subd9_12_13, List.forall_mem_cons.2 ⟨subd9_12_14, List.forall_mem_cons.2 ⟨subd9_12_15, List.forall_mem_cons.2 ⟨subd9_12_16, List.forall_mem_cons.2 ⟨subd9_12_17, List.forall_mem_cons.2 ⟨subd9_12_18, List.forall_mem_cons.2 ⟨subd9_12_19, List.forall_mem_cons.2 ⟨subd9_12_20, List.forall_mem_cons.2 ⟨subd9_12_21, List.forall_mem_cons.2 ⟨subd9_12_22, List.forall_mem_cons.2 ⟨subd9_12_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_13 : ldCheck G d9_13.U d9_13.ms ldd9_13 = true := by decide +kernel
theorem pre_okd9_13 : subPre G cell9 d9_13 = true := by decide +kernel
theorem subd9_13_0 : subd9_13 [-2] = true := by decide +kernel
theorem subd9_13_1 : subd9_13 [-1, -3] = true := by decide +kernel
theorem subd9_13_2 : subd9_13 [-1, -2] = true := by decide +kernel
theorem subd9_13_3 : subd9_13 [-1, -1] = true := by decide +kernel
theorem subd9_13_4 : subd9_13 [-1, 0] = true := by decide +kernel
theorem subd9_13_5 : subd9_13 [-1, 1] = true := by decide +kernel
theorem subd9_13_6 : subd9_13 [-1, 2] = true := by decide +kernel
theorem subd9_13_7 : subd9_13 [0, -3] = true := by decide +kernel
theorem subd9_13_8 : subd9_13 [0, -2] = true := by decide +kernel
theorem subd9_13_9 : subd9_13 [0, -1] = true := by decide +kernel
theorem subd9_13_10 : subd9_13 [0, 0] = true := by decide +kernel
theorem subd9_13_11 : subd9_13 [0, 1] = true := by decide +kernel
theorem subd9_13_12 : subd9_13 [0, 2] = true := by decide +kernel
theorem subd9_13_13 : subd9_13 [1, -3] = true := by decide +kernel
theorem subd9_13_14 : subd9_13 [1, -2] = true := by decide +kernel
theorem subd9_13_15 : subd9_13 [1, -1] = true := by decide +kernel
theorem subd9_13_16 : subd9_13 [1, 0] = true := by decide +kernel
theorem subd9_13_17 : subd9_13 [1, 1] = true := by decide +kernel
theorem subd9_13_18 : subd9_13 [1, 2] = true := by decide +kernel
theorem subd9_13_19 : subd9_13 [2] = true := by decide +kernel
theorem sbd9_13_0 : ∀ q ∈ blkd9_13_0, subd9_13 q = true := by
  unfold blkd9_13_0
  exact List.forall_mem_cons.2 ⟨subd9_13_0, List.forall_mem_cons.2 ⟨subd9_13_1, List.forall_mem_cons.2 ⟨subd9_13_2, List.forall_mem_cons.2 ⟨subd9_13_3, List.forall_mem_cons.2 ⟨subd9_13_4, List.forall_mem_cons.2 ⟨subd9_13_5, List.forall_mem_cons.2 ⟨subd9_13_6, List.forall_mem_cons.2 ⟨subd9_13_7, List.forall_mem_cons.2 ⟨subd9_13_8, List.forall_mem_cons.2 ⟨subd9_13_9, List.forall_mem_cons.2 ⟨subd9_13_10, List.forall_mem_cons.2 ⟨subd9_13_11, List.forall_mem_cons.2 ⟨subd9_13_12, List.forall_mem_cons.2 ⟨subd9_13_13, List.forall_mem_cons.2 ⟨subd9_13_14, List.forall_mem_cons.2 ⟨subd9_13_15, List.forall_mem_cons.2 ⟨subd9_13_16, List.forall_mem_cons.2 ⟨subd9_13_17, List.forall_mem_cons.2 ⟨subd9_13_18, List.forall_mem_cons.2 ⟨subd9_13_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_14 : ldCheck G d9_14.U d9_14.ms ldd9_14 = true := by decide +kernel
theorem pre_okd9_14 : subPre G cell9 d9_14 = true := by decide +kernel
theorem subd9_14_0 : subd9_14 [-5] = true := by decide +kernel
theorem subd9_14_1 : subd9_14 [-4, -3] = true := by decide +kernel
theorem subd9_14_2 : subd9_14 [-4, -2] = true := by decide +kernel
theorem subd9_14_3 : subd9_14 [-4, -1] = true := by decide +kernel
theorem subd9_14_4 : subd9_14 [-4, 0] = true := by decide +kernel
theorem subd9_14_5 : subd9_14 [-4, 1] = true := by decide +kernel
theorem subd9_14_6 : subd9_14 [-4, 2] = true := by decide +kernel
theorem subd9_14_7 : subd9_14 [-4, 3] = true := by decide +kernel
theorem subd9_14_8 : subd9_14 [-3, -4] = true := by decide +kernel
theorem subd9_14_9 : subd9_14 [-3, -3] = true := by decide +kernel
theorem subd9_14_10 : subd9_14 [-3, -2] = true := by decide +kernel
theorem subd9_14_11 : subd9_14 [-3, -1] = true := by decide +kernel
theorem subd9_14_12 : subd9_14 [-3, 0] = true := by decide +kernel
theorem subd9_14_13 : subd9_14 [-3, 1] = true := by decide +kernel
theorem subd9_14_14 : subd9_14 [-3, 2] = true := by decide +kernel
theorem subd9_14_15 : subd9_14 [-3, 3] = true := by decide +kernel
theorem subd9_14_16 : subd9_14 [-3, 4] = true := by decide +kernel
theorem subd9_14_17 : subd9_14 [-2, -5] = true := by decide +kernel
theorem subd9_14_18 : subd9_14 [-2, -4] = true := by decide +kernel
theorem subd9_14_19 : subd9_14 [-2, -3] = true := by decide +kernel
theorem subd9_14_20 : subd9_14 [-2, -2] = true := by decide +kernel
theorem subd9_14_21 : subd9_14 [-2, -1] = true := by decide +kernel
theorem subd9_14_22 : subd9_14 [-2, 0] = true := by decide +kernel
theorem subd9_14_23 : subd9_14 [-2, 1] = true := by decide +kernel
theorem subd9_14_24 : subd9_14 [-2, 2] = true := by decide +kernel
theorem subd9_14_25 : subd9_14 [-2, 3] = true := by decide +kernel
theorem subd9_14_26 : subd9_14 [-2, 4] = true := by decide +kernel
theorem subd9_14_27 : subd9_14 [-1, -5] = true := by decide +kernel
theorem subd9_14_28 : subd9_14 [-1, -4] = true := by decide +kernel
theorem subd9_14_29 : subd9_14 [-1, -3] = true := by decide +kernel
theorem subd9_14_30 : subd9_14 [-1, -2] = true := by decide +kernel
theorem subd9_14_31 : subd9_14 [-1, -1] = true := by decide +kernel
theorem sbd9_14_0 : ∀ q ∈ blkd9_14_0, subd9_14 q = true := by
  unfold blkd9_14_0
  exact List.forall_mem_cons.2 ⟨subd9_14_0, List.forall_mem_cons.2 ⟨subd9_14_1, List.forall_mem_cons.2 ⟨subd9_14_2, List.forall_mem_cons.2 ⟨subd9_14_3, List.forall_mem_cons.2 ⟨subd9_14_4, List.forall_mem_cons.2 ⟨subd9_14_5, List.forall_mem_cons.2 ⟨subd9_14_6, List.forall_mem_cons.2 ⟨subd9_14_7, List.forall_mem_cons.2 ⟨subd9_14_8, List.forall_mem_cons.2 ⟨subd9_14_9, List.forall_mem_cons.2 ⟨subd9_14_10, List.forall_mem_cons.2 ⟨subd9_14_11, List.forall_mem_cons.2 ⟨subd9_14_12, List.forall_mem_cons.2 ⟨subd9_14_13, List.forall_mem_cons.2 ⟨subd9_14_14, List.forall_mem_cons.2 ⟨subd9_14_15, List.forall_mem_cons.2 ⟨subd9_14_16, List.forall_mem_cons.2 ⟨subd9_14_17, List.forall_mem_cons.2 ⟨subd9_14_18, List.forall_mem_cons.2 ⟨subd9_14_19, List.forall_mem_cons.2 ⟨subd9_14_20, List.forall_mem_cons.2 ⟨subd9_14_21, List.forall_mem_cons.2 ⟨subd9_14_22, List.forall_mem_cons.2 ⟨subd9_14_23, List.forall_mem_cons.2 ⟨subd9_14_24, List.forall_mem_cons.2 ⟨subd9_14_25, List.forall_mem_cons.2 ⟨subd9_14_26, List.forall_mem_cons.2 ⟨subd9_14_27, List.forall_mem_cons.2 ⟨subd9_14_28, List.forall_mem_cons.2 ⟨subd9_14_29, List.forall_mem_cons.2 ⟨subd9_14_30, List.forall_mem_cons.2 ⟨subd9_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_14_32 : subd9_14 [-1, 0] = true := by decide +kernel
theorem subd9_14_33 : subd9_14 [-1, 1] = true := by decide +kernel
theorem subd9_14_34 : subd9_14 [-1, 2] = true := by decide +kernel
theorem subd9_14_35 : subd9_14 [-1, 3] = true := by decide +kernel
theorem subd9_14_36 : subd9_14 [-1, 4] = true := by decide +kernel
theorem subd9_14_37 : subd9_14 [0, -5] = true := by decide +kernel
theorem subd9_14_38 : subd9_14 [0, -4] = true := by decide +kernel
theorem subd9_14_39 : subd9_14 [0, -3] = true := by decide +kernel
theorem subd9_14_40 : subd9_14 [0, -2] = true := by decide +kernel
theorem subd9_14_41 : subd9_14 [0, -1] = true := by decide +kernel
theorem subd9_14_42 : subd9_14 [0, 0] = true := by decide +kernel
theorem subd9_14_43 : subd9_14 [0, 1] = true := by decide +kernel
theorem subd9_14_44 : subd9_14 [0, 2] = true := by decide +kernel
theorem subd9_14_45 : subd9_14 [0, 3] = true := by decide +kernel
theorem subd9_14_46 : subd9_14 [0, 4] = true := by decide +kernel
theorem subd9_14_47 : subd9_14 [1, -5] = true := by decide +kernel
theorem subd9_14_48 : subd9_14 [1, -4] = true := by decide +kernel
theorem subd9_14_49 : subd9_14 [1, -3] = true := by decide +kernel
theorem subd9_14_50 : subd9_14 [1, -2] = true := by decide +kernel
theorem subd9_14_51 : subd9_14 [1, -1] = true := by decide +kernel
theorem subd9_14_52 : subd9_14 [1, 0] = true := by decide +kernel
theorem subd9_14_53 : subd9_14 [1, 1] = true := by decide +kernel
theorem subd9_14_54 : subd9_14 [1, 2] = true := by decide +kernel
theorem subd9_14_55 : subd9_14 [1, 3] = true := by decide +kernel
theorem subd9_14_56 : subd9_14 [1, 4] = true := by decide +kernel
theorem subd9_14_57 : subd9_14 [2, -5] = true := by decide +kernel
theorem subd9_14_58 : subd9_14 [2, -4] = true := by decide +kernel
theorem subd9_14_59 : subd9_14 [2, -3] = true := by decide +kernel
theorem subd9_14_60 : subd9_14 [2, -2] = true := by decide +kernel
theorem subd9_14_61 : subd9_14 [2, -1] = true := by decide +kernel
theorem subd9_14_62 : subd9_14 [2, 0] = true := by decide +kernel
theorem subd9_14_63 : subd9_14 [2, 1] = true := by decide +kernel
theorem sbd9_14_1 : ∀ q ∈ blkd9_14_1, subd9_14 q = true := by
  unfold blkd9_14_1
  exact List.forall_mem_cons.2 ⟨subd9_14_32, List.forall_mem_cons.2 ⟨subd9_14_33, List.forall_mem_cons.2 ⟨subd9_14_34, List.forall_mem_cons.2 ⟨subd9_14_35, List.forall_mem_cons.2 ⟨subd9_14_36, List.forall_mem_cons.2 ⟨subd9_14_37, List.forall_mem_cons.2 ⟨subd9_14_38, List.forall_mem_cons.2 ⟨subd9_14_39, List.forall_mem_cons.2 ⟨subd9_14_40, List.forall_mem_cons.2 ⟨subd9_14_41, List.forall_mem_cons.2 ⟨subd9_14_42, List.forall_mem_cons.2 ⟨subd9_14_43, List.forall_mem_cons.2 ⟨subd9_14_44, List.forall_mem_cons.2 ⟨subd9_14_45, List.forall_mem_cons.2 ⟨subd9_14_46, List.forall_mem_cons.2 ⟨subd9_14_47, List.forall_mem_cons.2 ⟨subd9_14_48, List.forall_mem_cons.2 ⟨subd9_14_49, List.forall_mem_cons.2 ⟨subd9_14_50, List.forall_mem_cons.2 ⟨subd9_14_51, List.forall_mem_cons.2 ⟨subd9_14_52, List.forall_mem_cons.2 ⟨subd9_14_53, List.forall_mem_cons.2 ⟨subd9_14_54, List.forall_mem_cons.2 ⟨subd9_14_55, List.forall_mem_cons.2 ⟨subd9_14_56, List.forall_mem_cons.2 ⟨subd9_14_57, List.forall_mem_cons.2 ⟨subd9_14_58, List.forall_mem_cons.2 ⟨subd9_14_59, List.forall_mem_cons.2 ⟨subd9_14_60, List.forall_mem_cons.2 ⟨subd9_14_61, List.forall_mem_cons.2 ⟨subd9_14_62, List.forall_mem_cons.2 ⟨subd9_14_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
