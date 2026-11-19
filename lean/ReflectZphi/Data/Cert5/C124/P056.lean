import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-3] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-2] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [-1, -4] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [-1, -3] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [-1, -2] = true := by decide +kernel
theorem subd10_7_5 : subd10_7 [-1, -1] = true := by decide +kernel
theorem subd10_7_6 : subd10_7 [-1, 0] = true := by decide +kernel
theorem subd10_7_7 : subd10_7 [-1, 1] = true := by decide +kernel
theorem subd10_7_8 : subd10_7 [-1, 2] = true := by decide +kernel
theorem subd10_7_9 : subd10_7 [-1, 3] = true := by decide +kernel
theorem subd10_7_10 : subd10_7 [0, -4] = true := by decide +kernel
theorem subd10_7_11 : subd10_7 [0, -3] = true := by decide +kernel
theorem subd10_7_12 : subd10_7 [0, -2] = true := by decide +kernel
theorem subd10_7_13 : subd10_7 [0, -1] = true := by decide +kernel
theorem subd10_7_14 : subd10_7 [0, 0] = true := by decide +kernel
theorem subd10_7_15 : subd10_7 [0, 1] = true := by decide +kernel
theorem subd10_7_16 : subd10_7 [0, 2] = true := by decide +kernel
theorem subd10_7_17 : subd10_7 [0, 3] = true := by decide +kernel
theorem subd10_7_18 : subd10_7 [1, -4] = true := by decide +kernel
theorem subd10_7_19 : subd10_7 [1, -3] = true := by decide +kernel
theorem subd10_7_20 : subd10_7 [1, -2] = true := by decide +kernel
theorem subd10_7_21 : subd10_7 [1, -1] = true := by decide +kernel
theorem subd10_7_22 : subd10_7 [1, 0] = true := by decide +kernel
theorem subd10_7_23 : subd10_7 [1, 1] = true := by decide +kernel
theorem subd10_7_24 : subd10_7 [1, 2] = true := by decide +kernel
theorem subd10_7_25 : subd10_7 [1, 3] = true := by decide +kernel
theorem subd10_7_26 : subd10_7 [2] = true := by decide +kernel
theorem subd10_7_27 : subd10_7 [3] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_cons.2 ⟨subd10_7_5, List.forall_mem_cons.2 ⟨subd10_7_6, List.forall_mem_cons.2 ⟨subd10_7_7, List.forall_mem_cons.2 ⟨subd10_7_8, List.forall_mem_cons.2 ⟨subd10_7_9, List.forall_mem_cons.2 ⟨subd10_7_10, List.forall_mem_cons.2 ⟨subd10_7_11, List.forall_mem_cons.2 ⟨subd10_7_12, List.forall_mem_cons.2 ⟨subd10_7_13, List.forall_mem_cons.2 ⟨subd10_7_14, List.forall_mem_cons.2 ⟨subd10_7_15, List.forall_mem_cons.2 ⟨subd10_7_16, List.forall_mem_cons.2 ⟨subd10_7_17, List.forall_mem_cons.2 ⟨subd10_7_18, List.forall_mem_cons.2 ⟨subd10_7_19, List.forall_mem_cons.2 ⟨subd10_7_20, List.forall_mem_cons.2 ⟨subd10_7_21, List.forall_mem_cons.2 ⟨subd10_7_22, List.forall_mem_cons.2 ⟨subd10_7_23, List.forall_mem_cons.2 ⟨subd10_7_24, List.forall_mem_cons.2 ⟨subd10_7_25, List.forall_mem_cons.2 ⟨subd10_7_26, List.forall_mem_cons.2 ⟨subd10_7_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_8 : ldCheck G d10_8.U d10_8.ms ldd10_8 = true := by decide +kernel
theorem pre_okd10_8 : subPre G cell10 d10_8 = true := by decide +kernel
theorem subd10_8_0 : subd10_8 [-1, -2] = true := by decide +kernel
theorem subd10_8_1 : subd10_8 [-1, -1] = true := by decide +kernel
theorem subd10_8_2 : subd10_8 [-1, 0, -8] = true := by decide +kernel
theorem subd10_8_3 : subd10_8 [-1, 0, -7] = true := by decide +kernel
theorem subd10_8_4 : subd10_8 [-1, 0, -6] = true := by decide +kernel
theorem subd10_8_5 : subd10_8 [-1, 0, -5] = true := by decide +kernel
theorem subd10_8_6 : subd10_8 [-1, 0, -4] = true := by decide +kernel
theorem subd10_8_7 : subd10_8 [-1, 0, -3] = true := by decide +kernel
theorem subd10_8_8 : subd10_8 [-1, 0, -2] = true := by decide +kernel
theorem subd10_8_9 : subd10_8 [-1, 0, -1] = true := by decide +kernel
theorem subd10_8_10 : subd10_8 [-1, 0, 0] = true := by decide +kernel
theorem subd10_8_11 : subd10_8 [-1, 0, 1] = true := by decide +kernel
theorem subd10_8_12 : subd10_8 [-1, 0, 2] = true := by decide +kernel
theorem subd10_8_13 : subd10_8 [-1, 0, 3] = true := by decide +kernel
theorem subd10_8_14 : subd10_8 [-1, 0, 4] = true := by decide +kernel
theorem subd10_8_15 : subd10_8 [-1, 0, 5] = true := by decide +kernel
theorem subd10_8_16 : subd10_8 [-1, 0, 6] = true := by decide +kernel
theorem subd10_8_17 : subd10_8 [-1, 0, 7] = true := by decide +kernel
theorem subd10_8_18 : subd10_8 [0, -2] = true := by decide +kernel
theorem subd10_8_19 : subd10_8 [0, -1, -8] = true := by decide +kernel
theorem subd10_8_20 : subd10_8 [0, -1, -7] = true := by decide +kernel
theorem subd10_8_21 : subd10_8 [0, -1, -6] = true := by decide +kernel
theorem subd10_8_22 : subd10_8 [0, -1, -5] = true := by decide +kernel
theorem subd10_8_23 : subd10_8 [0, -1, -4] = true := by decide +kernel
theorem subd10_8_24 : subd10_8 [0, -1, -3] = true := by decide +kernel
theorem subd10_8_25 : subd10_8 [0, -1, -2] = true := by decide +kernel
theorem subd10_8_26 : subd10_8 [0, -1, -1] = true := by decide +kernel
theorem subd10_8_27 : subd10_8 [0, -1, 0] = true := by decide +kernel
theorem subd10_8_28 : subd10_8 [0, -1, 1] = true := by decide +kernel
theorem subd10_8_29 : subd10_8 [0, -1, 2] = true := by decide +kernel
theorem subd10_8_30 : subd10_8 [0, -1, 3] = true := by decide +kernel
theorem subd10_8_31 : subd10_8 [0, -1, 4] = true := by decide +kernel
theorem sbd10_8_0 : ∀ q ∈ blkd10_8_0, subd10_8 q = true := by
  unfold blkd10_8_0
  exact List.forall_mem_cons.2 ⟨subd10_8_0, List.forall_mem_cons.2 ⟨subd10_8_1, List.forall_mem_cons.2 ⟨subd10_8_2, List.forall_mem_cons.2 ⟨subd10_8_3, List.forall_mem_cons.2 ⟨subd10_8_4, List.forall_mem_cons.2 ⟨subd10_8_5, List.forall_mem_cons.2 ⟨subd10_8_6, List.forall_mem_cons.2 ⟨subd10_8_7, List.forall_mem_cons.2 ⟨subd10_8_8, List.forall_mem_cons.2 ⟨subd10_8_9, List.forall_mem_cons.2 ⟨subd10_8_10, List.forall_mem_cons.2 ⟨subd10_8_11, List.forall_mem_cons.2 ⟨subd10_8_12, List.forall_mem_cons.2 ⟨subd10_8_13, List.forall_mem_cons.2 ⟨subd10_8_14, List.forall_mem_cons.2 ⟨subd10_8_15, List.forall_mem_cons.2 ⟨subd10_8_16, List.forall_mem_cons.2 ⟨subd10_8_17, List.forall_mem_cons.2 ⟨subd10_8_18, List.forall_mem_cons.2 ⟨subd10_8_19, List.forall_mem_cons.2 ⟨subd10_8_20, List.forall_mem_cons.2 ⟨subd10_8_21, List.forall_mem_cons.2 ⟨subd10_8_22, List.forall_mem_cons.2 ⟨subd10_8_23, List.forall_mem_cons.2 ⟨subd10_8_24, List.forall_mem_cons.2 ⟨subd10_8_25, List.forall_mem_cons.2 ⟨subd10_8_26, List.forall_mem_cons.2 ⟨subd10_8_27, List.forall_mem_cons.2 ⟨subd10_8_28, List.forall_mem_cons.2 ⟨subd10_8_29, List.forall_mem_cons.2 ⟨subd10_8_30, List.forall_mem_cons.2 ⟨subd10_8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_8_32 : subd10_8 [0, -1, 5] = true := by decide +kernel
theorem subd10_8_33 : subd10_8 [0, -1, 6] = true := by decide +kernel
theorem subd10_8_34 : subd10_8 [0, -1, 7] = true := by decide +kernel
theorem subd10_8_35 : subd10_8 [0, -1, 8] = true := by decide +kernel
theorem subd10_8_36 : subd10_8 [0, 0, -11] = true := by decide +kernel
theorem subd10_8_37 : subd10_8 [0, 0, -10] = true := by decide +kernel
theorem subd10_8_38 : subd10_8 [0, 0, -9] = true := by decide +kernel
theorem subd10_8_39 : subd10_8 [0, 0, -8] = true := by decide +kernel
theorem subd10_8_40 : subd10_8 [0, 0, -7] = true := by decide +kernel
theorem subd10_8_41 : subd10_8 [0, 0, -6] = true := by decide +kernel
theorem subd10_8_42 : subd10_8 [0, 0, -5] = true := by decide +kernel
theorem subd10_8_43 : subd10_8 [0, 0, -4] = true := by decide +kernel
theorem subd10_8_44 : subd10_8 [0, 0, -3] = true := by decide +kernel
theorem subd10_8_45 : subd10_8 [0, 0, -2] = true := by decide +kernel
theorem subd10_8_46 : subd10_8 [0, 0, -1] = true := by decide +kernel
theorem subd10_8_47 : subd10_8 [0, 0, 0] = true := by decide +kernel
theorem subd10_8_48 : subd10_8 [0, 0, 1] = true := by decide +kernel
theorem subd10_8_49 : subd10_8 [0, 0, 2] = true := by decide +kernel
theorem subd10_8_50 : subd10_8 [0, 0, 3] = true := by decide +kernel
theorem subd10_8_51 : subd10_8 [0, 0, 4] = true := by decide +kernel
theorem subd10_8_52 : subd10_8 [0, 0, 5] = true := by decide +kernel
theorem subd10_8_53 : subd10_8 [0, 0, 6] = true := by decide +kernel
theorem subd10_8_54 : subd10_8 [0, 0, 7] = true := by decide +kernel
theorem subd10_8_55 : subd10_8 [0, 0, 8] = true := by decide +kernel
theorem subd10_8_56 : subd10_8 [0, 0, 9] = true := by decide +kernel
theorem subd10_8_57 : subd10_8 [0, 0, 10] = true := by decide +kernel
theorem subd10_8_58 : subd10_8 [0, 1, -9] = true := by decide +kernel
theorem subd10_8_59 : subd10_8 [0, 1, -8] = true := by decide +kernel
theorem subd10_8_60 : subd10_8 [0, 1, -7] = true := by decide +kernel
theorem subd10_8_61 : subd10_8 [0, 1, -6] = true := by decide +kernel
theorem subd10_8_62 : subd10_8 [0, 1, -5] = true := by decide +kernel
theorem subd10_8_63 : subd10_8 [0, 1, -4] = true := by decide +kernel
theorem sbd10_8_1 : ∀ q ∈ blkd10_8_1, subd10_8 q = true := by
  unfold blkd10_8_1
  exact List.forall_mem_cons.2 ⟨subd10_8_32, List.forall_mem_cons.2 ⟨subd10_8_33, List.forall_mem_cons.2 ⟨subd10_8_34, List.forall_mem_cons.2 ⟨subd10_8_35, List.forall_mem_cons.2 ⟨subd10_8_36, List.forall_mem_cons.2 ⟨subd10_8_37, List.forall_mem_cons.2 ⟨subd10_8_38, List.forall_mem_cons.2 ⟨subd10_8_39, List.forall_mem_cons.2 ⟨subd10_8_40, List.forall_mem_cons.2 ⟨subd10_8_41, List.forall_mem_cons.2 ⟨subd10_8_42, List.forall_mem_cons.2 ⟨subd10_8_43, List.forall_mem_cons.2 ⟨subd10_8_44, List.forall_mem_cons.2 ⟨subd10_8_45, List.forall_mem_cons.2 ⟨subd10_8_46, List.forall_mem_cons.2 ⟨subd10_8_47, List.forall_mem_cons.2 ⟨subd10_8_48, List.forall_mem_cons.2 ⟨subd10_8_49, List.forall_mem_cons.2 ⟨subd10_8_50, List.forall_mem_cons.2 ⟨subd10_8_51, List.forall_mem_cons.2 ⟨subd10_8_52, List.forall_mem_cons.2 ⟨subd10_8_53, List.forall_mem_cons.2 ⟨subd10_8_54, List.forall_mem_cons.2 ⟨subd10_8_55, List.forall_mem_cons.2 ⟨subd10_8_56, List.forall_mem_cons.2 ⟨subd10_8_57, List.forall_mem_cons.2 ⟨subd10_8_58, List.forall_mem_cons.2 ⟨subd10_8_59, List.forall_mem_cons.2 ⟨subd10_8_60, List.forall_mem_cons.2 ⟨subd10_8_61, List.forall_mem_cons.2 ⟨subd10_8_62, List.forall_mem_cons.2 ⟨subd10_8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_8_64 : subd10_8 [0, 1, -3] = true := by decide +kernel
theorem subd10_8_65 : subd10_8 [0, 1, -2] = true := by decide +kernel
theorem subd10_8_66 : subd10_8 [0, 1, -1] = true := by decide +kernel
theorem subd10_8_67 : subd10_8 [0, 1, 0] = true := by decide +kernel
theorem subd10_8_68 : subd10_8 [0, 1, 1] = true := by decide +kernel
theorem subd10_8_69 : subd10_8 [0, 1, 2] = true := by decide +kernel
theorem subd10_8_70 : subd10_8 [0, 1, 3] = true := by decide +kernel
theorem subd10_8_71 : subd10_8 [0, 1, 4] = true := by decide +kernel
theorem subd10_8_72 : subd10_8 [0, 1, 5] = true := by decide +kernel
theorem subd10_8_73 : subd10_8 [0, 1, 6] = true := by decide +kernel
theorem subd10_8_74 : subd10_8 [0, 1, 7] = true := by decide +kernel
theorem subd10_8_75 : subd10_8 [1, -1] = true := by decide +kernel
theorem subd10_8_76 : subd10_8 [1, 0, -8] = true := by decide +kernel
theorem subd10_8_77 : subd10_8 [1, 0, -7] = true := by decide +kernel
theorem subd10_8_78 : subd10_8 [1, 0, -6] = true := by decide +kernel
theorem subd10_8_79 : subd10_8 [1, 0, -5] = true := by decide +kernel
theorem subd10_8_80 : subd10_8 [1, 0, -4] = true := by decide +kernel
theorem subd10_8_81 : subd10_8 [1, 0, -3] = true := by decide +kernel
theorem subd10_8_82 : subd10_8 [1, 0, -2] = true := by decide +kernel
theorem subd10_8_83 : subd10_8 [1, 0, -1] = true := by decide +kernel
theorem subd10_8_84 : subd10_8 [1, 0, 0] = true := by decide +kernel
theorem subd10_8_85 : subd10_8 [1, 0, 1] = true := by decide +kernel
theorem subd10_8_86 : subd10_8 [1, 0, 2] = true := by decide +kernel
theorem subd10_8_87 : subd10_8 [1, 0, 3] = true := by decide +kernel
theorem subd10_8_88 : subd10_8 [1, 0, 4] = true := by decide +kernel
theorem subd10_8_89 : subd10_8 [1, 0, 5] = true := by decide +kernel
theorem subd10_8_90 : subd10_8 [1, 0, 6] = true := by decide +kernel
theorem subd10_8_91 : subd10_8 [1, 0, 7] = true := by decide +kernel
theorem subd10_8_92 : subd10_8 [1, 1] = true := by decide +kernel
theorem sbd10_8_2 : ∀ q ∈ blkd10_8_2, subd10_8 q = true := by
  unfold blkd10_8_2
  exact List.forall_mem_cons.2 ⟨subd10_8_64, List.forall_mem_cons.2 ⟨subd10_8_65, List.forall_mem_cons.2 ⟨subd10_8_66, List.forall_mem_cons.2 ⟨subd10_8_67, List.forall_mem_cons.2 ⟨subd10_8_68, List.forall_mem_cons.2 ⟨subd10_8_69, List.forall_mem_cons.2 ⟨subd10_8_70, List.forall_mem_cons.2 ⟨subd10_8_71, List.forall_mem_cons.2 ⟨subd10_8_72, List.forall_mem_cons.2 ⟨subd10_8_73, List.forall_mem_cons.2 ⟨subd10_8_74, List.forall_mem_cons.2 ⟨subd10_8_75, List.forall_mem_cons.2 ⟨subd10_8_76, List.forall_mem_cons.2 ⟨subd10_8_77, List.forall_mem_cons.2 ⟨subd10_8_78, List.forall_mem_cons.2 ⟨subd10_8_79, List.forall_mem_cons.2 ⟨subd10_8_80, List.forall_mem_cons.2 ⟨subd10_8_81, List.forall_mem_cons.2 ⟨subd10_8_82, List.forall_mem_cons.2 ⟨subd10_8_83, List.forall_mem_cons.2 ⟨subd10_8_84, List.forall_mem_cons.2 ⟨subd10_8_85, List.forall_mem_cons.2 ⟨subd10_8_86, List.forall_mem_cons.2 ⟨subd10_8_87, List.forall_mem_cons.2 ⟨subd10_8_88, List.forall_mem_cons.2 ⟨subd10_8_89, List.forall_mem_cons.2 ⟨subd10_8_90, List.forall_mem_cons.2 ⟨subd10_8_91, List.forall_mem_cons.2 ⟨subd10_8_92, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_9 : ldCheck G d10_9.U d10_9.ms ldd10_9 = true := by decide +kernel
theorem pre_okd10_9 : subPre G cell10 d10_9 = true := by decide +kernel
theorem subd10_9_0 : subd10_9 [-2] = true := by decide +kernel
theorem subd10_9_1 : subd10_9 [-1, -3] = true := by decide +kernel
theorem subd10_9_2 : subd10_9 [-1, -2] = true := by decide +kernel
theorem subd10_9_3 : subd10_9 [-1, -1] = true := by decide +kernel
theorem subd10_9_4 : subd10_9 [-1, 0] = true := by decide +kernel
theorem subd10_9_5 : subd10_9 [-1, 1] = true := by decide +kernel
theorem subd10_9_6 : subd10_9 [-1, 2] = true := by decide +kernel
theorem subd10_9_7 : subd10_9 [0, -3] = true := by decide +kernel
theorem subd10_9_8 : subd10_9 [0, -2] = true := by decide +kernel
theorem subd10_9_9 : subd10_9 [0, -1] = true := by decide +kernel
theorem subd10_9_10 : subd10_9 [0, 0] = true := by decide +kernel
theorem subd10_9_11 : subd10_9 [0, 1] = true := by decide +kernel
theorem subd10_9_12 : subd10_9 [0, 2] = true := by decide +kernel
theorem subd10_9_13 : subd10_9 [1, -3] = true := by decide +kernel
theorem subd10_9_14 : subd10_9 [1, -2] = true := by decide +kernel
theorem subd10_9_15 : subd10_9 [1, -1] = true := by decide +kernel
theorem subd10_9_16 : subd10_9 [1, 0] = true := by decide +kernel
theorem subd10_9_17 : subd10_9 [1, 1] = true := by decide +kernel
theorem subd10_9_18 : subd10_9 [1, 2] = true := by decide +kernel
theorem subd10_9_19 : subd10_9 [2] = true := by decide +kernel
theorem sbd10_9_0 : ∀ q ∈ blkd10_9_0, subd10_9 q = true := by
  unfold blkd10_9_0
  exact List.forall_mem_cons.2 ⟨subd10_9_0, List.forall_mem_cons.2 ⟨subd10_9_1, List.forall_mem_cons.2 ⟨subd10_9_2, List.forall_mem_cons.2 ⟨subd10_9_3, List.forall_mem_cons.2 ⟨subd10_9_4, List.forall_mem_cons.2 ⟨subd10_9_5, List.forall_mem_cons.2 ⟨subd10_9_6, List.forall_mem_cons.2 ⟨subd10_9_7, List.forall_mem_cons.2 ⟨subd10_9_8, List.forall_mem_cons.2 ⟨subd10_9_9, List.forall_mem_cons.2 ⟨subd10_9_10, List.forall_mem_cons.2 ⟨subd10_9_11, List.forall_mem_cons.2 ⟨subd10_9_12, List.forall_mem_cons.2 ⟨subd10_9_13, List.forall_mem_cons.2 ⟨subd10_9_14, List.forall_mem_cons.2 ⟨subd10_9_15, List.forall_mem_cons.2 ⟨subd10_9_16, List.forall_mem_cons.2 ⟨subd10_9_17, List.forall_mem_cons.2 ⟨subd10_9_18, List.forall_mem_cons.2 ⟨subd10_9_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_10 : ldCheck G d10_10.U d10_10.ms ldd10_10 = true := by decide +kernel
theorem pre_okd10_10 : subPre G cell10 d10_10 = true := by decide +kernel
theorem subd10_10_0 : subd10_10 [-3] = true := by decide +kernel
theorem subd10_10_1 : subd10_10 [-2] = true := by decide +kernel
theorem subd10_10_2 : subd10_10 [-1] = true := by decide +kernel
theorem subd10_10_3 : subd10_10 [0, -4] = true := by decide +kernel
theorem subd10_10_4 : subd10_10 [0, -3] = true := by decide +kernel
theorem subd10_10_5 : subd10_10 [0, -2] = true := by decide +kernel
theorem subd10_10_6 : subd10_10 [0, -1] = true := by decide +kernel
theorem subd10_10_7 : subd10_10 [0, 0] = true := by decide +kernel
theorem subd10_10_8 : subd10_10 [0, 1] = true := by decide +kernel
theorem subd10_10_9 : subd10_10 [0, 2] = true := by decide +kernel
theorem subd10_10_10 : subd10_10 [0, 3] = true := by decide +kernel
theorem subd10_10_11 : subd10_10 [1] = true := by decide +kernel
theorem subd10_10_12 : subd10_10 [2] = true := by decide +kernel
theorem subd10_10_13 : subd10_10 [3] = true := by decide +kernel
theorem sbd10_10_0 : ∀ q ∈ blkd10_10_0, subd10_10 q = true := by
  unfold blkd10_10_0
  exact List.forall_mem_cons.2 ⟨subd10_10_0, List.forall_mem_cons.2 ⟨subd10_10_1, List.forall_mem_cons.2 ⟨subd10_10_2, List.forall_mem_cons.2 ⟨subd10_10_3, List.forall_mem_cons.2 ⟨subd10_10_4, List.forall_mem_cons.2 ⟨subd10_10_5, List.forall_mem_cons.2 ⟨subd10_10_6, List.forall_mem_cons.2 ⟨subd10_10_7, List.forall_mem_cons.2 ⟨subd10_10_8, List.forall_mem_cons.2 ⟨subd10_10_9, List.forall_mem_cons.2 ⟨subd10_10_10, List.forall_mem_cons.2 ⟨subd10_10_11, List.forall_mem_cons.2 ⟨subd10_10_12, List.forall_mem_cons.2 ⟨subd10_10_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
