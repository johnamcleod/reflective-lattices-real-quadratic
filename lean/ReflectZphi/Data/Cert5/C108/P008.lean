import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_4_0 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-1, -1] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-1, 0, -7] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-1, 0, -6] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-1, 0, -5] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-1, 0, -4] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-1, 0, -3] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-1, 0, -2] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [-1, 0, -1] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [-1, 0, 0] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [-1, 0, 1] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [-1, 0, 2] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [-1, 0, 3] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [-1, 0, 4] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [-1, 0, 5] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [-1, 0, 6] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [0, -1, -8] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [0, -1, -7] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [0, -1, -6] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [0, -1, -5] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [0, -1, -4] = true := by decide +kernel
theorem subd7_4_22 : subd7_4 [0, -1, -3] = true := by decide +kernel
theorem subd7_4_23 : subd7_4 [0, -1, -2] = true := by decide +kernel
theorem subd7_4_24 : subd7_4 [0, -1, -1] = true := by decide +kernel
theorem subd7_4_25 : subd7_4 [0, -1, 0] = true := by decide +kernel
theorem subd7_4_26 : subd7_4 [0, -1, 1] = true := by decide +kernel
theorem subd7_4_27 : subd7_4 [0, -1, 2] = true := by decide +kernel
theorem subd7_4_28 : subd7_4 [0, -1, 3] = true := by decide +kernel
theorem subd7_4_29 : subd7_4 [0, -1, 4] = true := by decide +kernel
theorem subd7_4_30 : subd7_4 [0, -1, 5] = true := by decide +kernel
theorem subd7_4_31 : subd7_4 [0, -1, 6] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_cons.2 ⟨subd7_4_22, List.forall_mem_cons.2 ⟨subd7_4_23, List.forall_mem_cons.2 ⟨subd7_4_24, List.forall_mem_cons.2 ⟨subd7_4_25, List.forall_mem_cons.2 ⟨subd7_4_26, List.forall_mem_cons.2 ⟨subd7_4_27, List.forall_mem_cons.2 ⟨subd7_4_28, List.forall_mem_cons.2 ⟨subd7_4_29, List.forall_mem_cons.2 ⟨subd7_4_30, List.forall_mem_cons.2 ⟨subd7_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_32 : subd7_4 [0, -1, 7] = true := by decide +kernel
theorem subd7_4_33 : subd7_4 [0, 0, -10] = true := by decide +kernel
theorem subd7_4_34 : subd7_4 [0, 0, -9] = true := by decide +kernel
theorem subd7_4_35 : subd7_4 [0, 0, -8] = true := by decide +kernel
theorem subd7_4_36 : subd7_4 [0, 0, -7] = true := by decide +kernel
theorem subd7_4_37 : subd7_4 [0, 0, -6] = true := by decide +kernel
theorem subd7_4_38 : subd7_4 [0, 0, -5] = true := by decide +kernel
theorem subd7_4_39 : subd7_4 [0, 0, -4] = true := by decide +kernel
theorem subd7_4_40 : subd7_4 [0, 0, -3] = true := by decide +kernel
theorem subd7_4_41 : subd7_4 [0, 0, -2] = true := by decide +kernel
theorem subd7_4_42 : subd7_4 [0, 0, -1] = true := by decide +kernel
theorem subd7_4_43 : subd7_4 [0, 0, 0] = true := by decide +kernel
theorem subd7_4_44 : subd7_4 [0, 0, 1] = true := by decide +kernel
theorem subd7_4_45 : subd7_4 [0, 0, 2] = true := by decide +kernel
theorem subd7_4_46 : subd7_4 [0, 0, 3] = true := by decide +kernel
theorem subd7_4_47 : subd7_4 [0, 0, 4] = true := by decide +kernel
theorem subd7_4_48 : subd7_4 [0, 0, 5] = true := by decide +kernel
theorem subd7_4_49 : subd7_4 [0, 0, 6] = true := by decide +kernel
theorem subd7_4_50 : subd7_4 [0, 0, 7] = true := by decide +kernel
theorem subd7_4_51 : subd7_4 [0, 0, 8] = true := by decide +kernel
theorem subd7_4_52 : subd7_4 [0, 0, 9] = true := by decide +kernel
theorem subd7_4_53 : subd7_4 [0, 1, -8] = true := by decide +kernel
theorem subd7_4_54 : subd7_4 [0, 1, -7] = true := by decide +kernel
theorem subd7_4_55 : subd7_4 [0, 1, -6] = true := by decide +kernel
theorem subd7_4_56 : subd7_4 [0, 1, -5] = true := by decide +kernel
theorem subd7_4_57 : subd7_4 [0, 1, -4] = true := by decide +kernel
theorem subd7_4_58 : subd7_4 [0, 1, -3] = true := by decide +kernel
theorem subd7_4_59 : subd7_4 [0, 1, -2] = true := by decide +kernel
theorem subd7_4_60 : subd7_4 [0, 1, -1] = true := by decide +kernel
theorem subd7_4_61 : subd7_4 [0, 1, 0] = true := by decide +kernel
theorem subd7_4_62 : subd7_4 [0, 1, 1] = true := by decide +kernel
theorem subd7_4_63 : subd7_4 [0, 1, 2] = true := by decide +kernel
theorem sbd7_4_1 : ∀ q ∈ blkd7_4_1, subd7_4 q = true := by
  unfold blkd7_4_1
  exact List.forall_mem_cons.2 ⟨subd7_4_32, List.forall_mem_cons.2 ⟨subd7_4_33, List.forall_mem_cons.2 ⟨subd7_4_34, List.forall_mem_cons.2 ⟨subd7_4_35, List.forall_mem_cons.2 ⟨subd7_4_36, List.forall_mem_cons.2 ⟨subd7_4_37, List.forall_mem_cons.2 ⟨subd7_4_38, List.forall_mem_cons.2 ⟨subd7_4_39, List.forall_mem_cons.2 ⟨subd7_4_40, List.forall_mem_cons.2 ⟨subd7_4_41, List.forall_mem_cons.2 ⟨subd7_4_42, List.forall_mem_cons.2 ⟨subd7_4_43, List.forall_mem_cons.2 ⟨subd7_4_44, List.forall_mem_cons.2 ⟨subd7_4_45, List.forall_mem_cons.2 ⟨subd7_4_46, List.forall_mem_cons.2 ⟨subd7_4_47, List.forall_mem_cons.2 ⟨subd7_4_48, List.forall_mem_cons.2 ⟨subd7_4_49, List.forall_mem_cons.2 ⟨subd7_4_50, List.forall_mem_cons.2 ⟨subd7_4_51, List.forall_mem_cons.2 ⟨subd7_4_52, List.forall_mem_cons.2 ⟨subd7_4_53, List.forall_mem_cons.2 ⟨subd7_4_54, List.forall_mem_cons.2 ⟨subd7_4_55, List.forall_mem_cons.2 ⟨subd7_4_56, List.forall_mem_cons.2 ⟨subd7_4_57, List.forall_mem_cons.2 ⟨subd7_4_58, List.forall_mem_cons.2 ⟨subd7_4_59, List.forall_mem_cons.2 ⟨subd7_4_60, List.forall_mem_cons.2 ⟨subd7_4_61, List.forall_mem_cons.2 ⟨subd7_4_62, List.forall_mem_cons.2 ⟨subd7_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_64 : subd7_4 [0, 1, 3] = true := by decide +kernel
theorem subd7_4_65 : subd7_4 [0, 1, 4] = true := by decide +kernel
theorem subd7_4_66 : subd7_4 [0, 1, 5] = true := by decide +kernel
theorem subd7_4_67 : subd7_4 [0, 1, 6] = true := by decide +kernel
theorem subd7_4_68 : subd7_4 [0, 1, 7] = true := by decide +kernel
theorem subd7_4_69 : subd7_4 [1, -1] = true := by decide +kernel
theorem subd7_4_70 : subd7_4 [1, 0, -7] = true := by decide +kernel
theorem subd7_4_71 : subd7_4 [1, 0, -6] = true := by decide +kernel
theorem subd7_4_72 : subd7_4 [1, 0, -5] = true := by decide +kernel
theorem subd7_4_73 : subd7_4 [1, 0, -4] = true := by decide +kernel
theorem subd7_4_74 : subd7_4 [1, 0, -3] = true := by decide +kernel
theorem subd7_4_75 : subd7_4 [1, 0, -2] = true := by decide +kernel
theorem subd7_4_76 : subd7_4 [1, 0, -1] = true := by decide +kernel
theorem subd7_4_77 : subd7_4 [1, 0, 0] = true := by decide +kernel
theorem subd7_4_78 : subd7_4 [1, 0, 1] = true := by decide +kernel
theorem subd7_4_79 : subd7_4 [1, 0, 2] = true := by decide +kernel
theorem subd7_4_80 : subd7_4 [1, 0, 3] = true := by decide +kernel
theorem subd7_4_81 : subd7_4 [1, 0, 4] = true := by decide +kernel
theorem subd7_4_82 : subd7_4 [1, 0, 5] = true := by decide +kernel
theorem subd7_4_83 : subd7_4 [1, 0, 6] = true := by decide +kernel
theorem subd7_4_84 : subd7_4 [1, 1] = true := by decide +kernel
theorem sbd7_4_2 : ∀ q ∈ blkd7_4_2, subd7_4 q = true := by
  unfold blkd7_4_2
  exact List.forall_mem_cons.2 ⟨subd7_4_64, List.forall_mem_cons.2 ⟨subd7_4_65, List.forall_mem_cons.2 ⟨subd7_4_66, List.forall_mem_cons.2 ⟨subd7_4_67, List.forall_mem_cons.2 ⟨subd7_4_68, List.forall_mem_cons.2 ⟨subd7_4_69, List.forall_mem_cons.2 ⟨subd7_4_70, List.forall_mem_cons.2 ⟨subd7_4_71, List.forall_mem_cons.2 ⟨subd7_4_72, List.forall_mem_cons.2 ⟨subd7_4_73, List.forall_mem_cons.2 ⟨subd7_4_74, List.forall_mem_cons.2 ⟨subd7_4_75, List.forall_mem_cons.2 ⟨subd7_4_76, List.forall_mem_cons.2 ⟨subd7_4_77, List.forall_mem_cons.2 ⟨subd7_4_78, List.forall_mem_cons.2 ⟨subd7_4_79, List.forall_mem_cons.2 ⟨subd7_4_80, List.forall_mem_cons.2 ⟨subd7_4_81, List.forall_mem_cons.2 ⟨subd7_4_82, List.forall_mem_cons.2 ⟨subd7_4_83, List.forall_mem_cons.2 ⟨subd7_4_84, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-1, -2] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-1, -1] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-1, 0] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-1, 1] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [1, -1] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [1, 0] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [1, 1] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [2] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-2] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-1] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [1] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [-2] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-1] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [0] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [1] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [2] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2, -3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2, -2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-2, -1] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-2, 0] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-2, 1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-2, 2] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_20 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_21 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_22 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_23 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_24 : subd8_0 [2, -3] = true := by decide +kernel
theorem subd8_0_25 : subd8_0 [2, -2] = true := by decide +kernel
theorem subd8_0_26 : subd8_0 [2, -1] = true := by decide +kernel
theorem subd8_0_27 : subd8_0 [2, 0] = true := by decide +kernel
theorem subd8_0_28 : subd8_0 [2, 1] = true := by decide +kernel
theorem subd8_0_29 : subd8_0 [2, 2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_cons.2 ⟨subd8_0_20, List.forall_mem_cons.2 ⟨subd8_0_21, List.forall_mem_cons.2 ⟨subd8_0_22, List.forall_mem_cons.2 ⟨subd8_0_23, List.forall_mem_cons.2 ⟨subd8_0_24, List.forall_mem_cons.2 ⟨subd8_0_25, List.forall_mem_cons.2 ⟨subd8_0_26, List.forall_mem_cons.2 ⟨subd8_0_27, List.forall_mem_cons.2 ⟨subd8_0_28, List.forall_mem_cons.2 ⟨subd8_0_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C108
