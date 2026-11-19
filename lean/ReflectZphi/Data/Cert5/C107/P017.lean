import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_64 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_65 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_66 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_67 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_68 : subd8_3 [3, 2] = true := by decide +kernel
theorem subd8_3_69 : subd8_3 [4] = true := by decide +kernel
theorem sbd8_3_2 : ∀ q ∈ blkd8_3_2, subd8_3 q = true := by
  unfold blkd8_3_2
  exact List.forall_mem_cons.2 ⟨subd8_3_64, List.forall_mem_cons.2 ⟨subd8_3_65, List.forall_mem_cons.2 ⟨subd8_3_66, List.forall_mem_cons.2 ⟨subd8_3_67, List.forall_mem_cons.2 ⟨subd8_3_68, List.forall_mem_cons.2 ⟨subd8_3_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [-2] = true := by decide +kernel
theorem subd8_4_1 : subd8_4 [-1, -4] = true := by decide +kernel
theorem subd8_4_2 : subd8_4 [-1, -3] = true := by decide +kernel
theorem subd8_4_3 : subd8_4 [-1, -2] = true := by decide +kernel
theorem subd8_4_4 : subd8_4 [-1, -1] = true := by decide +kernel
theorem subd8_4_5 : subd8_4 [-1, 0] = true := by decide +kernel
theorem subd8_4_6 : subd8_4 [-1, 1] = true := by decide +kernel
theorem subd8_4_7 : subd8_4 [-1, 2] = true := by decide +kernel
theorem subd8_4_8 : subd8_4 [0, -4] = true := by decide +kernel
theorem subd8_4_9 : subd8_4 [0, -3] = true := by decide +kernel
theorem subd8_4_10 : subd8_4 [0, -2] = true := by decide +kernel
theorem subd8_4_11 : subd8_4 [0, -1] = true := by decide +kernel
theorem subd8_4_12 : subd8_4 [0, 0] = true := by decide +kernel
theorem subd8_4_13 : subd8_4 [0, 1] = true := by decide +kernel
theorem subd8_4_14 : subd8_4 [0, 2] = true := by decide +kernel
theorem subd8_4_15 : subd8_4 [0, 3] = true := by decide +kernel
theorem subd8_4_16 : subd8_4 [1, -3] = true := by decide +kernel
theorem subd8_4_17 : subd8_4 [1, -2] = true := by decide +kernel
theorem subd8_4_18 : subd8_4 [1, -1] = true := by decide +kernel
theorem subd8_4_19 : subd8_4 [1, 0] = true := by decide +kernel
theorem subd8_4_20 : subd8_4 [1, 1] = true := by decide +kernel
theorem subd8_4_21 : subd8_4 [1, 2] = true := by decide +kernel
theorem subd8_4_22 : subd8_4 [1, 3] = true := by decide +kernel
theorem subd8_4_23 : subd8_4 [2] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_cons.2 ⟨subd8_4_1, List.forall_mem_cons.2 ⟨subd8_4_2, List.forall_mem_cons.2 ⟨subd8_4_3, List.forall_mem_cons.2 ⟨subd8_4_4, List.forall_mem_cons.2 ⟨subd8_4_5, List.forall_mem_cons.2 ⟨subd8_4_6, List.forall_mem_cons.2 ⟨subd8_4_7, List.forall_mem_cons.2 ⟨subd8_4_8, List.forall_mem_cons.2 ⟨subd8_4_9, List.forall_mem_cons.2 ⟨subd8_4_10, List.forall_mem_cons.2 ⟨subd8_4_11, List.forall_mem_cons.2 ⟨subd8_4_12, List.forall_mem_cons.2 ⟨subd8_4_13, List.forall_mem_cons.2 ⟨subd8_4_14, List.forall_mem_cons.2 ⟨subd8_4_15, List.forall_mem_cons.2 ⟨subd8_4_16, List.forall_mem_cons.2 ⟨subd8_4_17, List.forall_mem_cons.2 ⟨subd8_4_18, List.forall_mem_cons.2 ⟨subd8_4_19, List.forall_mem_cons.2 ⟨subd8_4_20, List.forall_mem_cons.2 ⟨subd8_4_21, List.forall_mem_cons.2 ⟨subd8_4_22, List.forall_mem_cons.2 ⟨subd8_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [0] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [1] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-5] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-4, -3] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-4, -2] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-4, -1] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-4, 0] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-4, 1] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-4, 2] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [-4, 3] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [-3, -5] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [-3, -4] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [-3, -3] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [-3, -2] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [-3, -1] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [-3, 0] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [-3, 1] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [-3, 2] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [-3, 3] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [-3, 4] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [-2, -5] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [-2, -4] = true := by decide +kernel
theorem subd8_6_20 : subd8_6 [-2, -3] = true := by decide +kernel
theorem subd8_6_21 : subd8_6 [-2, -2] = true := by decide +kernel
theorem subd8_6_22 : subd8_6 [-2, -1] = true := by decide +kernel
theorem subd8_6_23 : subd8_6 [-2, 0] = true := by decide +kernel
theorem subd8_6_24 : subd8_6 [-2, 1] = true := by decide +kernel
theorem subd8_6_25 : subd8_6 [-2, 2] = true := by decide +kernel
theorem subd8_6_26 : subd8_6 [-2, 3] = true := by decide +kernel
theorem subd8_6_27 : subd8_6 [-2, 4] = true := by decide +kernel
theorem subd8_6_28 : subd8_6 [-1, -6] = true := by decide +kernel
theorem subd8_6_29 : subd8_6 [-1, -5] = true := by decide +kernel
theorem subd8_6_30 : subd8_6 [-1, -4] = true := by decide +kernel
theorem subd8_6_31 : subd8_6 [-1, -3] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_cons.2 ⟨subd8_6_20, List.forall_mem_cons.2 ⟨subd8_6_21, List.forall_mem_cons.2 ⟨subd8_6_22, List.forall_mem_cons.2 ⟨subd8_6_23, List.forall_mem_cons.2 ⟨subd8_6_24, List.forall_mem_cons.2 ⟨subd8_6_25, List.forall_mem_cons.2 ⟨subd8_6_26, List.forall_mem_cons.2 ⟨subd8_6_27, List.forall_mem_cons.2 ⟨subd8_6_28, List.forall_mem_cons.2 ⟨subd8_6_29, List.forall_mem_cons.2 ⟨subd8_6_30, List.forall_mem_cons.2 ⟨subd8_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_32 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_33 : subd8_6 [-1, -1] = true := by decide +kernel
theorem subd8_6_34 : subd8_6 [-1, 0] = true := by decide +kernel
theorem subd8_6_35 : subd8_6 [-1, 1] = true := by decide +kernel
theorem subd8_6_36 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_37 : subd8_6 [-1, 3] = true := by decide +kernel
theorem subd8_6_38 : subd8_6 [-1, 4] = true := by decide +kernel
theorem subd8_6_39 : subd8_6 [-1, 5] = true := by decide +kernel
theorem subd8_6_40 : subd8_6 [0, -6] = true := by decide +kernel
theorem subd8_6_41 : subd8_6 [0, -5] = true := by decide +kernel
theorem subd8_6_42 : subd8_6 [0, -4] = true := by decide +kernel
theorem subd8_6_43 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_44 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_45 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_46 : subd8_6 [0, 0] = true := by decide +kernel
theorem subd8_6_47 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_48 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_49 : subd8_6 [0, 3] = true := by decide +kernel
theorem subd8_6_50 : subd8_6 [0, 4] = true := by decide +kernel
theorem subd8_6_51 : subd8_6 [0, 5] = true := by decide +kernel
theorem subd8_6_52 : subd8_6 [1, -6] = true := by decide +kernel
theorem subd8_6_53 : subd8_6 [1, -5] = true := by decide +kernel
theorem subd8_6_54 : subd8_6 [1, -4] = true := by decide +kernel
theorem subd8_6_55 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_56 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_57 : subd8_6 [1, -1] = true := by decide +kernel
theorem subd8_6_58 : subd8_6 [1, 0] = true := by decide +kernel
theorem subd8_6_59 : subd8_6 [1, 1] = true := by decide +kernel
theorem subd8_6_60 : subd8_6 [1, 2] = true := by decide +kernel
theorem subd8_6_61 : subd8_6 [1, 3] = true := by decide +kernel
theorem subd8_6_62 : subd8_6 [1, 4] = true := by decide +kernel
theorem subd8_6_63 : subd8_6 [1, 5] = true := by decide +kernel
theorem sbd8_6_1 : ∀ q ∈ blkd8_6_1, subd8_6 q = true := by
  unfold blkd8_6_1
  exact List.forall_mem_cons.2 ⟨subd8_6_32, List.forall_mem_cons.2 ⟨subd8_6_33, List.forall_mem_cons.2 ⟨subd8_6_34, List.forall_mem_cons.2 ⟨subd8_6_35, List.forall_mem_cons.2 ⟨subd8_6_36, List.forall_mem_cons.2 ⟨subd8_6_37, List.forall_mem_cons.2 ⟨subd8_6_38, List.forall_mem_cons.2 ⟨subd8_6_39, List.forall_mem_cons.2 ⟨subd8_6_40, List.forall_mem_cons.2 ⟨subd8_6_41, List.forall_mem_cons.2 ⟨subd8_6_42, List.forall_mem_cons.2 ⟨subd8_6_43, List.forall_mem_cons.2 ⟨subd8_6_44, List.forall_mem_cons.2 ⟨subd8_6_45, List.forall_mem_cons.2 ⟨subd8_6_46, List.forall_mem_cons.2 ⟨subd8_6_47, List.forall_mem_cons.2 ⟨subd8_6_48, List.forall_mem_cons.2 ⟨subd8_6_49, List.forall_mem_cons.2 ⟨subd8_6_50, List.forall_mem_cons.2 ⟨subd8_6_51, List.forall_mem_cons.2 ⟨subd8_6_52, List.forall_mem_cons.2 ⟨subd8_6_53, List.forall_mem_cons.2 ⟨subd8_6_54, List.forall_mem_cons.2 ⟨subd8_6_55, List.forall_mem_cons.2 ⟨subd8_6_56, List.forall_mem_cons.2 ⟨subd8_6_57, List.forall_mem_cons.2 ⟨subd8_6_58, List.forall_mem_cons.2 ⟨subd8_6_59, List.forall_mem_cons.2 ⟨subd8_6_60, List.forall_mem_cons.2 ⟨subd8_6_61, List.forall_mem_cons.2 ⟨subd8_6_62, List.forall_mem_cons.2 ⟨subd8_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
