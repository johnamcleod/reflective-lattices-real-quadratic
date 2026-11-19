import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_0 : subd8_1 [-4] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-3, -5] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-3, -4] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-3, -3] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-3, -2] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-3, -1] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-3, 0] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-3, 1] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-2, -5] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-2, 3] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-1, -5] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [0, -5] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [0, -1] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [1, 4] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [2, -1] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [2, 4] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [3, 0] = true := by decide +kernel
theorem subd8_1_72 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_73 : subd8_1 [3, 2] = true := by decide +kernel
theorem subd8_1_74 : subd8_1 [3, 3] = true := by decide +kernel
theorem subd8_1_75 : subd8_1 [3, 4] = true := by decide +kernel
theorem subd8_1_76 : subd8_1 [4] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_cons.2 ⟨subd8_1_72, List.forall_mem_cons.2 ⟨subd8_1_73, List.forall_mem_cons.2 ⟨subd8_1_74, List.forall_mem_cons.2 ⟨subd8_1_75, List.forall_mem_cons.2 ⟨subd8_1_76, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-3] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-2, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-2, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-2, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-2, 2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-2, 3] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-1, -4] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-1, -3] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-1, -1, -6] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-1, -1, -5] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-1, -1, -4] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-1, -1, -3] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-1, -1, -2] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-1, -1, -1] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-1, -1, 0] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-1, -1, 1] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-1, -1, 2] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-1, -1, 3] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-1, -1, 4] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-1, -1, 5] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-1, -1, 6] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-1, -1, 7] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-1, 0, -7] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-1, 0, -6] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-1, 0, -5] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-1, 0, -4] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-1, 0, -3] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-1, 0, -2] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-1, 0, -1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_32 : subd8_2 [-1, 0, 0] = true := by decide +kernel
theorem subd8_2_33 : subd8_2 [-1, 0, 1] = true := by decide +kernel
theorem subd8_2_34 : subd8_2 [-1, 0, 2] = true := by decide +kernel
theorem subd8_2_35 : subd8_2 [-1, 0, 3] = true := by decide +kernel
theorem subd8_2_36 : subd8_2 [-1, 0, 4] = true := by decide +kernel
theorem subd8_2_37 : subd8_2 [-1, 0, 5] = true := by decide +kernel
theorem subd8_2_38 : subd8_2 [-1, 0, 6] = true := by decide +kernel
theorem subd8_2_39 : subd8_2 [-1, 0, 7] = true := by decide +kernel
theorem subd8_2_40 : subd8_2 [-1, 1, -7] = true := by decide +kernel
theorem subd8_2_41 : subd8_2 [-1, 1, -6] = true := by decide +kernel
theorem subd8_2_42 : subd8_2 [-1, 1, -5] = true := by decide +kernel
theorem subd8_2_43 : subd8_2 [-1, 1, -4] = true := by decide +kernel
theorem subd8_2_44 : subd8_2 [-1, 1, -3] = true := by decide +kernel
theorem subd8_2_45 : subd8_2 [-1, 1, -2] = true := by decide +kernel
theorem subd8_2_46 : subd8_2 [-1, 1, -1] = true := by decide +kernel
theorem subd8_2_47 : subd8_2 [-1, 1, 0] = true := by decide +kernel
theorem subd8_2_48 : subd8_2 [-1, 1, 1] = true := by decide +kernel
theorem subd8_2_49 : subd8_2 [-1, 1, 2] = true := by decide +kernel
theorem subd8_2_50 : subd8_2 [-1, 1, 3] = true := by decide +kernel
theorem subd8_2_51 : subd8_2 [-1, 1, 4] = true := by decide +kernel
theorem subd8_2_52 : subd8_2 [-1, 1, 5] = true := by decide +kernel
theorem subd8_2_53 : subd8_2 [-1, 1, 6] = true := by decide +kernel
theorem subd8_2_54 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_55 : subd8_2 [-1, 3] = true := by decide +kernel
theorem subd8_2_56 : subd8_2 [0, -4] = true := by decide +kernel
theorem subd8_2_57 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_58 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_59 : subd8_2 [0, -1, -7] = true := by decide +kernel
theorem subd8_2_60 : subd8_2 [0, -1, -6] = true := by decide +kernel
theorem subd8_2_61 : subd8_2 [0, -1, -5] = true := by decide +kernel
theorem subd8_2_62 : subd8_2 [0, -1, -4] = true := by decide +kernel
theorem subd8_2_63 : subd8_2 [0, -1, -3] = true := by decide +kernel
theorem sbd8_2_1 : ∀ q ∈ blkd8_2_1, subd8_2 q = true := by
  unfold blkd8_2_1
  exact List.forall_mem_cons.2 ⟨subd8_2_32, List.forall_mem_cons.2 ⟨subd8_2_33, List.forall_mem_cons.2 ⟨subd8_2_34, List.forall_mem_cons.2 ⟨subd8_2_35, List.forall_mem_cons.2 ⟨subd8_2_36, List.forall_mem_cons.2 ⟨subd8_2_37, List.forall_mem_cons.2 ⟨subd8_2_38, List.forall_mem_cons.2 ⟨subd8_2_39, List.forall_mem_cons.2 ⟨subd8_2_40, List.forall_mem_cons.2 ⟨subd8_2_41, List.forall_mem_cons.2 ⟨subd8_2_42, List.forall_mem_cons.2 ⟨subd8_2_43, List.forall_mem_cons.2 ⟨subd8_2_44, List.forall_mem_cons.2 ⟨subd8_2_45, List.forall_mem_cons.2 ⟨subd8_2_46, List.forall_mem_cons.2 ⟨subd8_2_47, List.forall_mem_cons.2 ⟨subd8_2_48, List.forall_mem_cons.2 ⟨subd8_2_49, List.forall_mem_cons.2 ⟨subd8_2_50, List.forall_mem_cons.2 ⟨subd8_2_51, List.forall_mem_cons.2 ⟨subd8_2_52, List.forall_mem_cons.2 ⟨subd8_2_53, List.forall_mem_cons.2 ⟨subd8_2_54, List.forall_mem_cons.2 ⟨subd8_2_55, List.forall_mem_cons.2 ⟨subd8_2_56, List.forall_mem_cons.2 ⟨subd8_2_57, List.forall_mem_cons.2 ⟨subd8_2_58, List.forall_mem_cons.2 ⟨subd8_2_59, List.forall_mem_cons.2 ⟨subd8_2_60, List.forall_mem_cons.2 ⟨subd8_2_61, List.forall_mem_cons.2 ⟨subd8_2_62, List.forall_mem_cons.2 ⟨subd8_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_64 : subd8_2 [0, -1, -2] = true := by decide +kernel
theorem subd8_2_65 : subd8_2 [0, -1, -1] = true := by decide +kernel
theorem subd8_2_66 : subd8_2 [0, -1, 0] = true := by decide +kernel
theorem subd8_2_67 : subd8_2 [0, -1, 1] = true := by decide +kernel
theorem subd8_2_68 : subd8_2 [0, -1, 2] = true := by decide +kernel
theorem subd8_2_69 : subd8_2 [0, -1, 3] = true := by decide +kernel
theorem subd8_2_70 : subd8_2 [0, -1, 4] = true := by decide +kernel
theorem subd8_2_71 : subd8_2 [0, -1, 5] = true := by decide +kernel
theorem subd8_2_72 : subd8_2 [0, -1, 6] = true := by decide +kernel
theorem subd8_2_73 : subd8_2 [0, -1, 7] = true := by decide +kernel
theorem subd8_2_74 : subd8_2 [0, 0, -8] = true := by decide +kernel
theorem subd8_2_75 : subd8_2 [0, 0, -7] = true := by decide +kernel
theorem subd8_2_76 : subd8_2 [0, 0, -6] = true := by decide +kernel
theorem subd8_2_77 : subd8_2 [0, 0, -5] = true := by decide +kernel
theorem subd8_2_78 : subd8_2 [0, 0, -4] = true := by decide +kernel
theorem subd8_2_79 : subd8_2 [0, 0, -3] = true := by decide +kernel
theorem subd8_2_80 : subd8_2 [0, 0, -2] = true := by decide +kernel
theorem subd8_2_81 : subd8_2 [0, 0, -1] = true := by decide +kernel
theorem subd8_2_82 : subd8_2 [0, 0, 0] = true := by decide +kernel
theorem subd8_2_83 : subd8_2 [0, 0, 1] = true := by decide +kernel
theorem subd8_2_84 : subd8_2 [0, 0, 2] = true := by decide +kernel
theorem subd8_2_85 : subd8_2 [0, 0, 3] = true := by decide +kernel
theorem subd8_2_86 : subd8_2 [0, 0, 4] = true := by decide +kernel
theorem subd8_2_87 : subd8_2 [0, 0, 5] = true := by decide +kernel
theorem subd8_2_88 : subd8_2 [0, 0, 6] = true := by decide +kernel
theorem subd8_2_89 : subd8_2 [0, 0, 7] = true := by decide +kernel
theorem subd8_2_90 : subd8_2 [0, 1, -8] = true := by decide +kernel
theorem subd8_2_91 : subd8_2 [0, 1, -7] = true := by decide +kernel
theorem subd8_2_92 : subd8_2 [0, 1, -6] = true := by decide +kernel
theorem subd8_2_93 : subd8_2 [0, 1, -5] = true := by decide +kernel
theorem subd8_2_94 : subd8_2 [0, 1, -4] = true := by decide +kernel
theorem subd8_2_95 : subd8_2 [0, 1, -3] = true := by decide +kernel
theorem sbd8_2_2 : ∀ q ∈ blkd8_2_2, subd8_2 q = true := by
  unfold blkd8_2_2
  exact List.forall_mem_cons.2 ⟨subd8_2_64, List.forall_mem_cons.2 ⟨subd8_2_65, List.forall_mem_cons.2 ⟨subd8_2_66, List.forall_mem_cons.2 ⟨subd8_2_67, List.forall_mem_cons.2 ⟨subd8_2_68, List.forall_mem_cons.2 ⟨subd8_2_69, List.forall_mem_cons.2 ⟨subd8_2_70, List.forall_mem_cons.2 ⟨subd8_2_71, List.forall_mem_cons.2 ⟨subd8_2_72, List.forall_mem_cons.2 ⟨subd8_2_73, List.forall_mem_cons.2 ⟨subd8_2_74, List.forall_mem_cons.2 ⟨subd8_2_75, List.forall_mem_cons.2 ⟨subd8_2_76, List.forall_mem_cons.2 ⟨subd8_2_77, List.forall_mem_cons.2 ⟨subd8_2_78, List.forall_mem_cons.2 ⟨subd8_2_79, List.forall_mem_cons.2 ⟨subd8_2_80, List.forall_mem_cons.2 ⟨subd8_2_81, List.forall_mem_cons.2 ⟨subd8_2_82, List.forall_mem_cons.2 ⟨subd8_2_83, List.forall_mem_cons.2 ⟨subd8_2_84, List.forall_mem_cons.2 ⟨subd8_2_85, List.forall_mem_cons.2 ⟨subd8_2_86, List.forall_mem_cons.2 ⟨subd8_2_87, List.forall_mem_cons.2 ⟨subd8_2_88, List.forall_mem_cons.2 ⟨subd8_2_89, List.forall_mem_cons.2 ⟨subd8_2_90, List.forall_mem_cons.2 ⟨subd8_2_91, List.forall_mem_cons.2 ⟨subd8_2_92, List.forall_mem_cons.2 ⟨subd8_2_93, List.forall_mem_cons.2 ⟨subd8_2_94, List.forall_mem_cons.2 ⟨subd8_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C136
