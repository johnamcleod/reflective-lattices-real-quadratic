import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_12 : ldCheck G d8_12.U d8_12.ms ldd8_12 = true := by decide +kernel
theorem pre_okd8_12 : subPre G cell8 d8_12 = true := by decide +kernel
theorem subd8_12_0 : subd8_12 [-2] = true := by decide +kernel
theorem subd8_12_1 : subd8_12 [-1, -4] = true := by decide +kernel
theorem subd8_12_2 : subd8_12 [-1, -3] = true := by decide +kernel
theorem subd8_12_3 : subd8_12 [-1, -2] = true := by decide +kernel
theorem subd8_12_4 : subd8_12 [-1, -1] = true := by decide +kernel
theorem subd8_12_5 : subd8_12 [-1, 0] = true := by decide +kernel
theorem subd8_12_6 : subd8_12 [-1, 1] = true := by decide +kernel
theorem subd8_12_7 : subd8_12 [-1, 2] = true := by decide +kernel
theorem subd8_12_8 : subd8_12 [0, -3] = true := by decide +kernel
theorem subd8_12_9 : subd8_12 [0, -2] = true := by decide +kernel
theorem subd8_12_10 : subd8_12 [0, -1] = true := by decide +kernel
theorem subd8_12_11 : subd8_12 [0, 0] = true := by decide +kernel
theorem subd8_12_12 : subd8_12 [0, 1] = true := by decide +kernel
theorem subd8_12_13 : subd8_12 [0, 2] = true := by decide +kernel
theorem subd8_12_14 : subd8_12 [1, -3] = true := by decide +kernel
theorem subd8_12_15 : subd8_12 [1, -2] = true := by decide +kernel
theorem subd8_12_16 : subd8_12 [1, -1] = true := by decide +kernel
theorem subd8_12_17 : subd8_12 [1, 0] = true := by decide +kernel
theorem subd8_12_18 : subd8_12 [1, 1] = true := by decide +kernel
theorem subd8_12_19 : subd8_12 [1, 2] = true := by decide +kernel
theorem subd8_12_20 : subd8_12 [1, 3] = true := by decide +kernel
theorem subd8_12_21 : subd8_12 [2] = true := by decide +kernel
theorem sbd8_12_0 : ∀ q ∈ blkd8_12_0, subd8_12 q = true := by
  unfold blkd8_12_0
  exact List.forall_mem_cons.2 ⟨subd8_12_0, List.forall_mem_cons.2 ⟨subd8_12_1, List.forall_mem_cons.2 ⟨subd8_12_2, List.forall_mem_cons.2 ⟨subd8_12_3, List.forall_mem_cons.2 ⟨subd8_12_4, List.forall_mem_cons.2 ⟨subd8_12_5, List.forall_mem_cons.2 ⟨subd8_12_6, List.forall_mem_cons.2 ⟨subd8_12_7, List.forall_mem_cons.2 ⟨subd8_12_8, List.forall_mem_cons.2 ⟨subd8_12_9, List.forall_mem_cons.2 ⟨subd8_12_10, List.forall_mem_cons.2 ⟨subd8_12_11, List.forall_mem_cons.2 ⟨subd8_12_12, List.forall_mem_cons.2 ⟨subd8_12_13, List.forall_mem_cons.2 ⟨subd8_12_14, List.forall_mem_cons.2 ⟨subd8_12_15, List.forall_mem_cons.2 ⟨subd8_12_16, List.forall_mem_cons.2 ⟨subd8_12_17, List.forall_mem_cons.2 ⟨subd8_12_18, List.forall_mem_cons.2 ⟨subd8_12_19, List.forall_mem_cons.2 ⟨subd8_12_20, List.forall_mem_cons.2 ⟨subd8_12_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_13 : ldCheck G d8_13.U d8_13.ms ldd8_13 = true := by decide +kernel
theorem pre_okd8_13 : subPre G cell8 d8_13 = true := by decide +kernel
theorem subd8_13_0 : subd8_13 [-3] = true := by decide +kernel
theorem subd8_13_1 : subd8_13 [-2, -4] = true := by decide +kernel
theorem subd8_13_2 : subd8_13 [-2, -3] = true := by decide +kernel
theorem subd8_13_3 : subd8_13 [-2, -2] = true := by decide +kernel
theorem subd8_13_4 : subd8_13 [-2, -1] = true := by decide +kernel
theorem subd8_13_5 : subd8_13 [-2, 0] = true := by decide +kernel
theorem subd8_13_6 : subd8_13 [-2, 1] = true := by decide +kernel
theorem subd8_13_7 : subd8_13 [-2, 2] = true := by decide +kernel
theorem subd8_13_8 : subd8_13 [-1, -4] = true := by decide +kernel
theorem subd8_13_9 : subd8_13 [-1, -3] = true := by decide +kernel
theorem subd8_13_10 : subd8_13 [-1, -2] = true := by decide +kernel
theorem subd8_13_11 : subd8_13 [-1, -1] = true := by decide +kernel
theorem subd8_13_12 : subd8_13 [-1, 0] = true := by decide +kernel
theorem subd8_13_13 : subd8_13 [-1, 1] = true := by decide +kernel
theorem subd8_13_14 : subd8_13 [-1, 2] = true := by decide +kernel
theorem subd8_13_15 : subd8_13 [-1, 3] = true := by decide +kernel
theorem subd8_13_16 : subd8_13 [0, -4] = true := by decide +kernel
theorem subd8_13_17 : subd8_13 [0, -3] = true := by decide +kernel
theorem subd8_13_18 : subd8_13 [0, -2] = true := by decide +kernel
theorem subd8_13_19 : subd8_13 [0, -1] = true := by decide +kernel
theorem subd8_13_20 : subd8_13 [0, 0] = true := by decide +kernel
theorem subd8_13_21 : subd8_13 [0, 1] = true := by decide +kernel
theorem subd8_13_22 : subd8_13 [0, 2] = true := by decide +kernel
theorem subd8_13_23 : subd8_13 [0, 3] = true := by decide +kernel
theorem subd8_13_24 : subd8_13 [1, -4] = true := by decide +kernel
theorem subd8_13_25 : subd8_13 [1, -3] = true := by decide +kernel
theorem subd8_13_26 : subd8_13 [1, -2] = true := by decide +kernel
theorem subd8_13_27 : subd8_13 [1, -1] = true := by decide +kernel
theorem subd8_13_28 : subd8_13 [1, 0] = true := by decide +kernel
theorem subd8_13_29 : subd8_13 [1, 1] = true := by decide +kernel
theorem subd8_13_30 : subd8_13 [1, 2] = true := by decide +kernel
theorem subd8_13_31 : subd8_13 [1, 3] = true := by decide +kernel
theorem sbd8_13_0 : ∀ q ∈ blkd8_13_0, subd8_13 q = true := by
  unfold blkd8_13_0
  exact List.forall_mem_cons.2 ⟨subd8_13_0, List.forall_mem_cons.2 ⟨subd8_13_1, List.forall_mem_cons.2 ⟨subd8_13_2, List.forall_mem_cons.2 ⟨subd8_13_3, List.forall_mem_cons.2 ⟨subd8_13_4, List.forall_mem_cons.2 ⟨subd8_13_5, List.forall_mem_cons.2 ⟨subd8_13_6, List.forall_mem_cons.2 ⟨subd8_13_7, List.forall_mem_cons.2 ⟨subd8_13_8, List.forall_mem_cons.2 ⟨subd8_13_9, List.forall_mem_cons.2 ⟨subd8_13_10, List.forall_mem_cons.2 ⟨subd8_13_11, List.forall_mem_cons.2 ⟨subd8_13_12, List.forall_mem_cons.2 ⟨subd8_13_13, List.forall_mem_cons.2 ⟨subd8_13_14, List.forall_mem_cons.2 ⟨subd8_13_15, List.forall_mem_cons.2 ⟨subd8_13_16, List.forall_mem_cons.2 ⟨subd8_13_17, List.forall_mem_cons.2 ⟨subd8_13_18, List.forall_mem_cons.2 ⟨subd8_13_19, List.forall_mem_cons.2 ⟨subd8_13_20, List.forall_mem_cons.2 ⟨subd8_13_21, List.forall_mem_cons.2 ⟨subd8_13_22, List.forall_mem_cons.2 ⟨subd8_13_23, List.forall_mem_cons.2 ⟨subd8_13_24, List.forall_mem_cons.2 ⟨subd8_13_25, List.forall_mem_cons.2 ⟨subd8_13_26, List.forall_mem_cons.2 ⟨subd8_13_27, List.forall_mem_cons.2 ⟨subd8_13_28, List.forall_mem_cons.2 ⟨subd8_13_29, List.forall_mem_cons.2 ⟨subd8_13_30, List.forall_mem_cons.2 ⟨subd8_13_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_13_32 : subd8_13 [2, -3] = true := by decide +kernel
theorem subd8_13_33 : subd8_13 [2, -2] = true := by decide +kernel
theorem subd8_13_34 : subd8_13 [2, -1] = true := by decide +kernel
theorem subd8_13_35 : subd8_13 [2, 0] = true := by decide +kernel
theorem subd8_13_36 : subd8_13 [2, 1] = true := by decide +kernel
theorem subd8_13_37 : subd8_13 [2, 2] = true := by decide +kernel
theorem subd8_13_38 : subd8_13 [2, 3] = true := by decide +kernel
theorem subd8_13_39 : subd8_13 [3] = true := by decide +kernel
theorem sbd8_13_1 : ∀ q ∈ blkd8_13_1, subd8_13 q = true := by
  unfold blkd8_13_1
  exact List.forall_mem_cons.2 ⟨subd8_13_32, List.forall_mem_cons.2 ⟨subd8_13_33, List.forall_mem_cons.2 ⟨subd8_13_34, List.forall_mem_cons.2 ⟨subd8_13_35, List.forall_mem_cons.2 ⟨subd8_13_36, List.forall_mem_cons.2 ⟨subd8_13_37, List.forall_mem_cons.2 ⟨subd8_13_38, List.forall_mem_cons.2 ⟨subd8_13_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_14 : ldCheck G d8_14.U d8_14.ms ldd8_14 = true := by decide +kernel
theorem pre_okd8_14 : subPre G cell8 d8_14 = true := by decide +kernel
theorem subd8_14_0 : subd8_14 [-5] = true := by decide +kernel
theorem subd8_14_1 : subd8_14 [-4, -3] = true := by decide +kernel
theorem subd8_14_2 : subd8_14 [-4, -2] = true := by decide +kernel
theorem subd8_14_3 : subd8_14 [-4, -1] = true := by decide +kernel
theorem subd8_14_4 : subd8_14 [-4, 0] = true := by decide +kernel
theorem subd8_14_5 : subd8_14 [-4, 1] = true := by decide +kernel
theorem subd8_14_6 : subd8_14 [-4, 2] = true := by decide +kernel
theorem subd8_14_7 : subd8_14 [-4, 3] = true := by decide +kernel
theorem subd8_14_8 : subd8_14 [-3, -4] = true := by decide +kernel
theorem subd8_14_9 : subd8_14 [-3, -3] = true := by decide +kernel
theorem subd8_14_10 : subd8_14 [-3, -2] = true := by decide +kernel
theorem subd8_14_11 : subd8_14 [-3, -1] = true := by decide +kernel
theorem subd8_14_12 : subd8_14 [-3, 0] = true := by decide +kernel
theorem subd8_14_13 : subd8_14 [-3, 1] = true := by decide +kernel
theorem subd8_14_14 : subd8_14 [-3, 2] = true := by decide +kernel
theorem subd8_14_15 : subd8_14 [-3, 3] = true := by decide +kernel
theorem subd8_14_16 : subd8_14 [-3, 4] = true := by decide +kernel
theorem subd8_14_17 : subd8_14 [-2, -5] = true := by decide +kernel
theorem subd8_14_18 : subd8_14 [-2, -4] = true := by decide +kernel
theorem subd8_14_19 : subd8_14 [-2, -3] = true := by decide +kernel
theorem subd8_14_20 : subd8_14 [-2, -2] = true := by decide +kernel
theorem subd8_14_21 : subd8_14 [-2, -1, -8] = true := by decide +kernel
theorem subd8_14_22 : subd8_14 [-2, -1, -7] = true := by decide +kernel
theorem subd8_14_23 : subd8_14 [-2, -1, -6] = true := by decide +kernel
theorem subd8_14_24 : subd8_14 [-2, -1, -5] = true := by decide +kernel
theorem subd8_14_25 : subd8_14 [-2, -1, -4] = true := by decide +kernel
theorem subd8_14_26 : subd8_14 [-2, -1, -3] = true := by decide +kernel
theorem subd8_14_27 : subd8_14 [-2, -1, -2] = true := by decide +kernel
theorem subd8_14_28 : subd8_14 [-2, -1, -1] = true := by decide +kernel
theorem subd8_14_29 : subd8_14 [-2, -1, 0] = true := by decide +kernel
theorem subd8_14_30 : subd8_14 [-2, -1, 1] = true := by decide +kernel
theorem subd8_14_31 : subd8_14 [-2, -1, 2] = true := by decide +kernel
theorem sbd8_14_0 : ∀ q ∈ blkd8_14_0, subd8_14 q = true := by
  unfold blkd8_14_0
  exact List.forall_mem_cons.2 ⟨subd8_14_0, List.forall_mem_cons.2 ⟨subd8_14_1, List.forall_mem_cons.2 ⟨subd8_14_2, List.forall_mem_cons.2 ⟨subd8_14_3, List.forall_mem_cons.2 ⟨subd8_14_4, List.forall_mem_cons.2 ⟨subd8_14_5, List.forall_mem_cons.2 ⟨subd8_14_6, List.forall_mem_cons.2 ⟨subd8_14_7, List.forall_mem_cons.2 ⟨subd8_14_8, List.forall_mem_cons.2 ⟨subd8_14_9, List.forall_mem_cons.2 ⟨subd8_14_10, List.forall_mem_cons.2 ⟨subd8_14_11, List.forall_mem_cons.2 ⟨subd8_14_12, List.forall_mem_cons.2 ⟨subd8_14_13, List.forall_mem_cons.2 ⟨subd8_14_14, List.forall_mem_cons.2 ⟨subd8_14_15, List.forall_mem_cons.2 ⟨subd8_14_16, List.forall_mem_cons.2 ⟨subd8_14_17, List.forall_mem_cons.2 ⟨subd8_14_18, List.forall_mem_cons.2 ⟨subd8_14_19, List.forall_mem_cons.2 ⟨subd8_14_20, List.forall_mem_cons.2 ⟨subd8_14_21, List.forall_mem_cons.2 ⟨subd8_14_22, List.forall_mem_cons.2 ⟨subd8_14_23, List.forall_mem_cons.2 ⟨subd8_14_24, List.forall_mem_cons.2 ⟨subd8_14_25, List.forall_mem_cons.2 ⟨subd8_14_26, List.forall_mem_cons.2 ⟨subd8_14_27, List.forall_mem_cons.2 ⟨subd8_14_28, List.forall_mem_cons.2 ⟨subd8_14_29, List.forall_mem_cons.2 ⟨subd8_14_30, List.forall_mem_cons.2 ⟨subd8_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_14_32 : subd8_14 [-2, -1, 3] = true := by decide +kernel
theorem subd8_14_33 : subd8_14 [-2, -1, 4] = true := by decide +kernel
theorem subd8_14_34 : subd8_14 [-2, -1, 5] = true := by decide +kernel
theorem subd8_14_35 : subd8_14 [-2, 0, -8] = true := by decide +kernel
theorem subd8_14_36 : subd8_14 [-2, 0, -7] = true := by decide +kernel
theorem subd8_14_37 : subd8_14 [-2, 0, -6] = true := by decide +kernel
theorem subd8_14_38 : subd8_14 [-2, 0, -5] = true := by decide +kernel
theorem subd8_14_39 : subd8_14 [-2, 0, -4] = true := by decide +kernel
theorem subd8_14_40 : subd8_14 [-2, 0, -3] = true := by decide +kernel
theorem subd8_14_41 : subd8_14 [-2, 0, -2] = true := by decide +kernel
theorem subd8_14_42 : subd8_14 [-2, 0, -1] = true := by decide +kernel
theorem subd8_14_43 : subd8_14 [-2, 0, 0] = true := by decide +kernel
theorem subd8_14_44 : subd8_14 [-2, 0, 1] = true := by decide +kernel
theorem subd8_14_45 : subd8_14 [-2, 0, 2] = true := by decide +kernel
theorem subd8_14_46 : subd8_14 [-2, 0, 3] = true := by decide +kernel
theorem subd8_14_47 : subd8_14 [-2, 0, 4] = true := by decide +kernel
theorem subd8_14_48 : subd8_14 [-2, 0, 5] = true := by decide +kernel
theorem subd8_14_49 : subd8_14 [-2, 0, 6] = true := by decide +kernel
theorem subd8_14_50 : subd8_14 [-2, 1, -8] = true := by decide +kernel
theorem subd8_14_51 : subd8_14 [-2, 1, -7] = true := by decide +kernel
theorem subd8_14_52 : subd8_14 [-2, 1, -6] = true := by decide +kernel
theorem subd8_14_53 : subd8_14 [-2, 1, -5] = true := by decide +kernel
theorem subd8_14_54 : subd8_14 [-2, 1, -4] = true := by decide +kernel
theorem subd8_14_55 : subd8_14 [-2, 1, -3] = true := by decide +kernel
theorem subd8_14_56 : subd8_14 [-2, 1, -2] = true := by decide +kernel
theorem subd8_14_57 : subd8_14 [-2, 1, -1] = true := by decide +kernel
theorem subd8_14_58 : subd8_14 [-2, 1, 0] = true := by decide +kernel
theorem subd8_14_59 : subd8_14 [-2, 1, 1] = true := by decide +kernel
theorem subd8_14_60 : subd8_14 [-2, 1, 2] = true := by decide +kernel
theorem subd8_14_61 : subd8_14 [-2, 1, 3] = true := by decide +kernel
theorem subd8_14_62 : subd8_14 [-2, 1, 4] = true := by decide +kernel
theorem subd8_14_63 : subd8_14 [-2, 1, 5] = true := by decide +kernel
theorem sbd8_14_1 : ∀ q ∈ blkd8_14_1, subd8_14 q = true := by
  unfold blkd8_14_1
  exact List.forall_mem_cons.2 ⟨subd8_14_32, List.forall_mem_cons.2 ⟨subd8_14_33, List.forall_mem_cons.2 ⟨subd8_14_34, List.forall_mem_cons.2 ⟨subd8_14_35, List.forall_mem_cons.2 ⟨subd8_14_36, List.forall_mem_cons.2 ⟨subd8_14_37, List.forall_mem_cons.2 ⟨subd8_14_38, List.forall_mem_cons.2 ⟨subd8_14_39, List.forall_mem_cons.2 ⟨subd8_14_40, List.forall_mem_cons.2 ⟨subd8_14_41, List.forall_mem_cons.2 ⟨subd8_14_42, List.forall_mem_cons.2 ⟨subd8_14_43, List.forall_mem_cons.2 ⟨subd8_14_44, List.forall_mem_cons.2 ⟨subd8_14_45, List.forall_mem_cons.2 ⟨subd8_14_46, List.forall_mem_cons.2 ⟨subd8_14_47, List.forall_mem_cons.2 ⟨subd8_14_48, List.forall_mem_cons.2 ⟨subd8_14_49, List.forall_mem_cons.2 ⟨subd8_14_50, List.forall_mem_cons.2 ⟨subd8_14_51, List.forall_mem_cons.2 ⟨subd8_14_52, List.forall_mem_cons.2 ⟨subd8_14_53, List.forall_mem_cons.2 ⟨subd8_14_54, List.forall_mem_cons.2 ⟨subd8_14_55, List.forall_mem_cons.2 ⟨subd8_14_56, List.forall_mem_cons.2 ⟨subd8_14_57, List.forall_mem_cons.2 ⟨subd8_14_58, List.forall_mem_cons.2 ⟨subd8_14_59, List.forall_mem_cons.2 ⟨subd8_14_60, List.forall_mem_cons.2 ⟨subd8_14_61, List.forall_mem_cons.2 ⟨subd8_14_62, List.forall_mem_cons.2 ⟨subd8_14_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
