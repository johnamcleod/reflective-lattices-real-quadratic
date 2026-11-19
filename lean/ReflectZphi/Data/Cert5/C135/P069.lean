import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-5] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-4, -5] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [-4, -4] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [-4, -3] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [-4, -2] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [-4, -1] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [-4, 0] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [-4, 1] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [-4, 2] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [-3, -5] = true := by decide +kernel
theorem subd10_6_10 : subd10_6 [-3, -4] = true := by decide +kernel
theorem subd10_6_11 : subd10_6 [-3, -3] = true := by decide +kernel
theorem subd10_6_12 : subd10_6 [-3, -2] = true := by decide +kernel
theorem subd10_6_13 : subd10_6 [-3, -1] = true := by decide +kernel
theorem subd10_6_14 : subd10_6 [-3, 0] = true := by decide +kernel
theorem subd10_6_15 : subd10_6 [-3, 1] = true := by decide +kernel
theorem subd10_6_16 : subd10_6 [-3, 2] = true := by decide +kernel
theorem subd10_6_17 : subd10_6 [-3, 3] = true := by decide +kernel
theorem subd10_6_18 : subd10_6 [-2, -6] = true := by decide +kernel
theorem subd10_6_19 : subd10_6 [-2, -5] = true := by decide +kernel
theorem subd10_6_20 : subd10_6 [-2, -4] = true := by decide +kernel
theorem subd10_6_21 : subd10_6 [-2, -3] = true := by decide +kernel
theorem subd10_6_22 : subd10_6 [-2, -2] = true := by decide +kernel
theorem subd10_6_23 : subd10_6 [-2, -1] = true := by decide +kernel
theorem subd10_6_24 : subd10_6 [-2, 0] = true := by decide +kernel
theorem subd10_6_25 : subd10_6 [-2, 1] = true := by decide +kernel
theorem subd10_6_26 : subd10_6 [-2, 2] = true := by decide +kernel
theorem subd10_6_27 : subd10_6 [-2, 3] = true := by decide +kernel
theorem subd10_6_28 : subd10_6 [-2, 4] = true := by decide +kernel
theorem subd10_6_29 : subd10_6 [-1, -6] = true := by decide +kernel
theorem subd10_6_30 : subd10_6 [-1, -5] = true := by decide +kernel
theorem subd10_6_31 : subd10_6 [-1, -4] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_cons.2 ⟨subd10_6_10, List.forall_mem_cons.2 ⟨subd10_6_11, List.forall_mem_cons.2 ⟨subd10_6_12, List.forall_mem_cons.2 ⟨subd10_6_13, List.forall_mem_cons.2 ⟨subd10_6_14, List.forall_mem_cons.2 ⟨subd10_6_15, List.forall_mem_cons.2 ⟨subd10_6_16, List.forall_mem_cons.2 ⟨subd10_6_17, List.forall_mem_cons.2 ⟨subd10_6_18, List.forall_mem_cons.2 ⟨subd10_6_19, List.forall_mem_cons.2 ⟨subd10_6_20, List.forall_mem_cons.2 ⟨subd10_6_21, List.forall_mem_cons.2 ⟨subd10_6_22, List.forall_mem_cons.2 ⟨subd10_6_23, List.forall_mem_cons.2 ⟨subd10_6_24, List.forall_mem_cons.2 ⟨subd10_6_25, List.forall_mem_cons.2 ⟨subd10_6_26, List.forall_mem_cons.2 ⟨subd10_6_27, List.forall_mem_cons.2 ⟨subd10_6_28, List.forall_mem_cons.2 ⟨subd10_6_29, List.forall_mem_cons.2 ⟨subd10_6_30, List.forall_mem_cons.2 ⟨subd10_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_32 : subd10_6 [-1, -3] = true := by decide +kernel
theorem subd10_6_33 : subd10_6 [-1, -2] = true := by decide +kernel
theorem subd10_6_34 : subd10_6 [-1, -1] = true := by decide +kernel
theorem subd10_6_35 : subd10_6 [-1, 0] = true := by decide +kernel
theorem subd10_6_36 : subd10_6 [-1, 1] = true := by decide +kernel
theorem subd10_6_37 : subd10_6 [-1, 2] = true := by decide +kernel
theorem subd10_6_38 : subd10_6 [-1, 3] = true := by decide +kernel
theorem subd10_6_39 : subd10_6 [-1, 4] = true := by decide +kernel
theorem subd10_6_40 : subd10_6 [0, -5] = true := by decide +kernel
theorem subd10_6_41 : subd10_6 [0, -4] = true := by decide +kernel
theorem subd10_6_42 : subd10_6 [0, -3] = true := by decide +kernel
theorem subd10_6_43 : subd10_6 [0, -2] = true := by decide +kernel
theorem subd10_6_44 : subd10_6 [0, -1] = true := by decide +kernel
theorem subd10_6_45 : subd10_6 [0, 0] = true := by decide +kernel
theorem subd10_6_46 : subd10_6 [0, 1] = true := by decide +kernel
theorem subd10_6_47 : subd10_6 [0, 2] = true := by decide +kernel
theorem subd10_6_48 : subd10_6 [0, 3] = true := by decide +kernel
theorem subd10_6_49 : subd10_6 [0, 4] = true := by decide +kernel
theorem subd10_6_50 : subd10_6 [1, -5] = true := by decide +kernel
theorem subd10_6_51 : subd10_6 [1, -4] = true := by decide +kernel
theorem subd10_6_52 : subd10_6 [1, -3] = true := by decide +kernel
theorem subd10_6_53 : subd10_6 [1, -2] = true := by decide +kernel
theorem subd10_6_54 : subd10_6 [1, -1] = true := by decide +kernel
theorem subd10_6_55 : subd10_6 [1, 0] = true := by decide +kernel
theorem subd10_6_56 : subd10_6 [1, 1] = true := by decide +kernel
theorem subd10_6_57 : subd10_6 [1, 2] = true := by decide +kernel
theorem subd10_6_58 : subd10_6 [1, 3] = true := by decide +kernel
theorem subd10_6_59 : subd10_6 [1, 4] = true := by decide +kernel
theorem subd10_6_60 : subd10_6 [1, 5] = true := by decide +kernel
theorem subd10_6_61 : subd10_6 [2, -5] = true := by decide +kernel
theorem subd10_6_62 : subd10_6 [2, -4] = true := by decide +kernel
theorem subd10_6_63 : subd10_6 [2, -3] = true := by decide +kernel
theorem sbd10_6_1 : ∀ q ∈ blkd10_6_1, subd10_6 q = true := by
  unfold blkd10_6_1
  exact List.forall_mem_cons.2 ⟨subd10_6_32, List.forall_mem_cons.2 ⟨subd10_6_33, List.forall_mem_cons.2 ⟨subd10_6_34, List.forall_mem_cons.2 ⟨subd10_6_35, List.forall_mem_cons.2 ⟨subd10_6_36, List.forall_mem_cons.2 ⟨subd10_6_37, List.forall_mem_cons.2 ⟨subd10_6_38, List.forall_mem_cons.2 ⟨subd10_6_39, List.forall_mem_cons.2 ⟨subd10_6_40, List.forall_mem_cons.2 ⟨subd10_6_41, List.forall_mem_cons.2 ⟨subd10_6_42, List.forall_mem_cons.2 ⟨subd10_6_43, List.forall_mem_cons.2 ⟨subd10_6_44, List.forall_mem_cons.2 ⟨subd10_6_45, List.forall_mem_cons.2 ⟨subd10_6_46, List.forall_mem_cons.2 ⟨subd10_6_47, List.forall_mem_cons.2 ⟨subd10_6_48, List.forall_mem_cons.2 ⟨subd10_6_49, List.forall_mem_cons.2 ⟨subd10_6_50, List.forall_mem_cons.2 ⟨subd10_6_51, List.forall_mem_cons.2 ⟨subd10_6_52, List.forall_mem_cons.2 ⟨subd10_6_53, List.forall_mem_cons.2 ⟨subd10_6_54, List.forall_mem_cons.2 ⟨subd10_6_55, List.forall_mem_cons.2 ⟨subd10_6_56, List.forall_mem_cons.2 ⟨subd10_6_57, List.forall_mem_cons.2 ⟨subd10_6_58, List.forall_mem_cons.2 ⟨subd10_6_59, List.forall_mem_cons.2 ⟨subd10_6_60, List.forall_mem_cons.2 ⟨subd10_6_61, List.forall_mem_cons.2 ⟨subd10_6_62, List.forall_mem_cons.2 ⟨subd10_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_64 : subd10_6 [2, -2] = true := by decide +kernel
theorem subd10_6_65 : subd10_6 [2, -1] = true := by decide +kernel
theorem subd10_6_66 : subd10_6 [2, 0] = true := by decide +kernel
theorem subd10_6_67 : subd10_6 [2, 1] = true := by decide +kernel
theorem subd10_6_68 : subd10_6 [2, 2] = true := by decide +kernel
theorem subd10_6_69 : subd10_6 [2, 3] = true := by decide +kernel
theorem subd10_6_70 : subd10_6 [2, 4] = true := by decide +kernel
theorem subd10_6_71 : subd10_6 [2, 5] = true := by decide +kernel
theorem subd10_6_72 : subd10_6 [3, -4] = true := by decide +kernel
theorem subd10_6_73 : subd10_6 [3, -3] = true := by decide +kernel
theorem subd10_6_74 : subd10_6 [3, -2] = true := by decide +kernel
theorem subd10_6_75 : subd10_6 [3, -1] = true := by decide +kernel
theorem subd10_6_76 : subd10_6 [3, 0] = true := by decide +kernel
theorem subd10_6_77 : subd10_6 [3, 1] = true := by decide +kernel
theorem subd10_6_78 : subd10_6 [3, 2] = true := by decide +kernel
theorem subd10_6_79 : subd10_6 [3, 3] = true := by decide +kernel
theorem subd10_6_80 : subd10_6 [3, 4] = true := by decide +kernel
theorem subd10_6_81 : subd10_6 [4, -3] = true := by decide +kernel
theorem subd10_6_82 : subd10_6 [4, -2] = true := by decide +kernel
theorem subd10_6_83 : subd10_6 [4, -1] = true := by decide +kernel
theorem subd10_6_84 : subd10_6 [4, 0] = true := by decide +kernel
theorem subd10_6_85 : subd10_6 [4, 1] = true := by decide +kernel
theorem subd10_6_86 : subd10_6 [4, 2] = true := by decide +kernel
theorem subd10_6_87 : subd10_6 [4, 3] = true := by decide +kernel
theorem subd10_6_88 : subd10_6 [4, 4] = true := by decide +kernel
theorem subd10_6_89 : subd10_6 [5] = true := by decide +kernel
theorem sbd10_6_2 : ∀ q ∈ blkd10_6_2, subd10_6 q = true := by
  unfold blkd10_6_2
  exact List.forall_mem_cons.2 ⟨subd10_6_64, List.forall_mem_cons.2 ⟨subd10_6_65, List.forall_mem_cons.2 ⟨subd10_6_66, List.forall_mem_cons.2 ⟨subd10_6_67, List.forall_mem_cons.2 ⟨subd10_6_68, List.forall_mem_cons.2 ⟨subd10_6_69, List.forall_mem_cons.2 ⟨subd10_6_70, List.forall_mem_cons.2 ⟨subd10_6_71, List.forall_mem_cons.2 ⟨subd10_6_72, List.forall_mem_cons.2 ⟨subd10_6_73, List.forall_mem_cons.2 ⟨subd10_6_74, List.forall_mem_cons.2 ⟨subd10_6_75, List.forall_mem_cons.2 ⟨subd10_6_76, List.forall_mem_cons.2 ⟨subd10_6_77, List.forall_mem_cons.2 ⟨subd10_6_78, List.forall_mem_cons.2 ⟨subd10_6_79, List.forall_mem_cons.2 ⟨subd10_6_80, List.forall_mem_cons.2 ⟨subd10_6_81, List.forall_mem_cons.2 ⟨subd10_6_82, List.forall_mem_cons.2 ⟨subd10_6_83, List.forall_mem_cons.2 ⟨subd10_6_84, List.forall_mem_cons.2 ⟨subd10_6_85, List.forall_mem_cons.2 ⟨subd10_6_86, List.forall_mem_cons.2 ⟨subd10_6_87, List.forall_mem_cons.2 ⟨subd10_6_88, List.forall_mem_cons.2 ⟨subd10_6_89, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-2, -3] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-2, -2] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [-2, -1] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [-2, 0, -9] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [-2, 0, -8] = true := by decide +kernel
theorem subd10_7_5 : subd10_7 [-2, 0, -7] = true := by decide +kernel
theorem subd10_7_6 : subd10_7 [-2, 0, -6] = true := by decide +kernel
theorem subd10_7_7 : subd10_7 [-2, 0, -5] = true := by decide +kernel
theorem subd10_7_8 : subd10_7 [-2, 0, -4] = true := by decide +kernel
theorem subd10_7_9 : subd10_7 [-2, 0, -3] = true := by decide +kernel
theorem subd10_7_10 : subd10_7 [-2, 0, -2] = true := by decide +kernel
theorem subd10_7_11 : subd10_7 [-2, 0, -1] = true := by decide +kernel
theorem subd10_7_12 : subd10_7 [-2, 0, 0] = true := by decide +kernel
theorem subd10_7_13 : subd10_7 [-2, 0, 1] = true := by decide +kernel
theorem subd10_7_14 : subd10_7 [-2, 0, 2] = true := by decide +kernel
theorem subd10_7_15 : subd10_7 [-2, 0, 3] = true := by decide +kernel
theorem subd10_7_16 : subd10_7 [-2, 0, 4] = true := by decide +kernel
theorem subd10_7_17 : subd10_7 [-2, 0, 5] = true := by decide +kernel
theorem subd10_7_18 : subd10_7 [-2, 0, 6] = true := by decide +kernel
theorem subd10_7_19 : subd10_7 [-2, 1] = true := by decide +kernel
theorem subd10_7_20 : subd10_7 [-2, 2] = true := by decide +kernel
theorem subd10_7_21 : subd10_7 [-1, -3] = true := by decide +kernel
theorem subd10_7_22 : subd10_7 [-1, -2, -8] = true := by decide +kernel
theorem subd10_7_23 : subd10_7 [-1, -2, -7] = true := by decide +kernel
theorem subd10_7_24 : subd10_7 [-1, -2, -6] = true := by decide +kernel
theorem subd10_7_25 : subd10_7 [-1, -2, -5] = true := by decide +kernel
theorem subd10_7_26 : subd10_7 [-1, -2, -4] = true := by decide +kernel
theorem subd10_7_27 : subd10_7 [-1, -2, -3] = true := by decide +kernel
theorem subd10_7_28 : subd10_7 [-1, -2, -2] = true := by decide +kernel
theorem subd10_7_29 : subd10_7 [-1, -2, -1] = true := by decide +kernel
theorem subd10_7_30 : subd10_7 [-1, -2, 0] = true := by decide +kernel
theorem subd10_7_31 : subd10_7 [-1, -2, 1] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_cons.2 ⟨subd10_7_5, List.forall_mem_cons.2 ⟨subd10_7_6, List.forall_mem_cons.2 ⟨subd10_7_7, List.forall_mem_cons.2 ⟨subd10_7_8, List.forall_mem_cons.2 ⟨subd10_7_9, List.forall_mem_cons.2 ⟨subd10_7_10, List.forall_mem_cons.2 ⟨subd10_7_11, List.forall_mem_cons.2 ⟨subd10_7_12, List.forall_mem_cons.2 ⟨subd10_7_13, List.forall_mem_cons.2 ⟨subd10_7_14, List.forall_mem_cons.2 ⟨subd10_7_15, List.forall_mem_cons.2 ⟨subd10_7_16, List.forall_mem_cons.2 ⟨subd10_7_17, List.forall_mem_cons.2 ⟨subd10_7_18, List.forall_mem_cons.2 ⟨subd10_7_19, List.forall_mem_cons.2 ⟨subd10_7_20, List.forall_mem_cons.2 ⟨subd10_7_21, List.forall_mem_cons.2 ⟨subd10_7_22, List.forall_mem_cons.2 ⟨subd10_7_23, List.forall_mem_cons.2 ⟨subd10_7_24, List.forall_mem_cons.2 ⟨subd10_7_25, List.forall_mem_cons.2 ⟨subd10_7_26, List.forall_mem_cons.2 ⟨subd10_7_27, List.forall_mem_cons.2 ⟨subd10_7_28, List.forall_mem_cons.2 ⟨subd10_7_29, List.forall_mem_cons.2 ⟨subd10_7_30, List.forall_mem_cons.2 ⟨subd10_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_32 : subd10_7 [-1, -2, 2] = true := by decide +kernel
theorem subd10_7_33 : subd10_7 [-1, -2, 3] = true := by decide +kernel
theorem subd10_7_34 : subd10_7 [-1, -2, 4] = true := by decide +kernel
theorem subd10_7_35 : subd10_7 [-1, -2, 5] = true := by decide +kernel
theorem subd10_7_36 : subd10_7 [-1, -2, 6] = true := by decide +kernel
theorem subd10_7_37 : subd10_7 [-1, -1, -10] = true := by decide +kernel
theorem subd10_7_38 : subd10_7 [-1, -1, -9] = true := by decide +kernel
theorem subd10_7_39 : subd10_7 [-1, -1, -8] = true := by decide +kernel
theorem subd10_7_40 : subd10_7 [-1, -1, -7] = true := by decide +kernel
theorem subd10_7_41 : subd10_7 [-1, -1, -6] = true := by decide +kernel
theorem subd10_7_42 : subd10_7 [-1, -1, -5] = true := by decide +kernel
theorem subd10_7_43 : subd10_7 [-1, -1, -4] = true := by decide +kernel
theorem subd10_7_44 : subd10_7 [-1, -1, -3] = true := by decide +kernel
theorem subd10_7_45 : subd10_7 [-1, -1, -2] = true := by decide +kernel
theorem subd10_7_46 : subd10_7 [-1, -1, -1] = true := by decide +kernel
theorem subd10_7_47 : subd10_7 [-1, -1, 0] = true := by decide +kernel
theorem subd10_7_48 : subd10_7 [-1, -1, 1] = true := by decide +kernel
theorem subd10_7_49 : subd10_7 [-1, -1, 2] = true := by decide +kernel
theorem subd10_7_50 : subd10_7 [-1, -1, 3] = true := by decide +kernel
theorem subd10_7_51 : subd10_7 [-1, -1, 4] = true := by decide +kernel
theorem subd10_7_52 : subd10_7 [-1, -1, 5] = true := by decide +kernel
theorem subd10_7_53 : subd10_7 [-1, -1, 6] = true := by decide +kernel
theorem subd10_7_54 : subd10_7 [-1, -1, 7] = true := by decide +kernel
theorem subd10_7_55 : subd10_7 [-1, -1, 8] = true := by decide +kernel
theorem subd10_7_56 : subd10_7 [-1, 0, -10] = true := by decide +kernel
theorem subd10_7_57 : subd10_7 [-1, 0, -9] = true := by decide +kernel
theorem subd10_7_58 : subd10_7 [-1, 0, -8] = true := by decide +kernel
theorem subd10_7_59 : subd10_7 [-1, 0, -7] = true := by decide +kernel
theorem subd10_7_60 : subd10_7 [-1, 0, -6] = true := by decide +kernel
theorem subd10_7_61 : subd10_7 [-1, 0, -5] = true := by decide +kernel
theorem subd10_7_62 : subd10_7 [-1, 0, -4] = true := by decide +kernel
theorem subd10_7_63 : subd10_7 [-1, 0, -3] = true := by decide +kernel
theorem sbd10_7_1 : ∀ q ∈ blkd10_7_1, subd10_7 q = true := by
  unfold blkd10_7_1
  exact List.forall_mem_cons.2 ⟨subd10_7_32, List.forall_mem_cons.2 ⟨subd10_7_33, List.forall_mem_cons.2 ⟨subd10_7_34, List.forall_mem_cons.2 ⟨subd10_7_35, List.forall_mem_cons.2 ⟨subd10_7_36, List.forall_mem_cons.2 ⟨subd10_7_37, List.forall_mem_cons.2 ⟨subd10_7_38, List.forall_mem_cons.2 ⟨subd10_7_39, List.forall_mem_cons.2 ⟨subd10_7_40, List.forall_mem_cons.2 ⟨subd10_7_41, List.forall_mem_cons.2 ⟨subd10_7_42, List.forall_mem_cons.2 ⟨subd10_7_43, List.forall_mem_cons.2 ⟨subd10_7_44, List.forall_mem_cons.2 ⟨subd10_7_45, List.forall_mem_cons.2 ⟨subd10_7_46, List.forall_mem_cons.2 ⟨subd10_7_47, List.forall_mem_cons.2 ⟨subd10_7_48, List.forall_mem_cons.2 ⟨subd10_7_49, List.forall_mem_cons.2 ⟨subd10_7_50, List.forall_mem_cons.2 ⟨subd10_7_51, List.forall_mem_cons.2 ⟨subd10_7_52, List.forall_mem_cons.2 ⟨subd10_7_53, List.forall_mem_cons.2 ⟨subd10_7_54, List.forall_mem_cons.2 ⟨subd10_7_55, List.forall_mem_cons.2 ⟨subd10_7_56, List.forall_mem_cons.2 ⟨subd10_7_57, List.forall_mem_cons.2 ⟨subd10_7_58, List.forall_mem_cons.2 ⟨subd10_7_59, List.forall_mem_cons.2 ⟨subd10_7_60, List.forall_mem_cons.2 ⟨subd10_7_61, List.forall_mem_cons.2 ⟨subd10_7_62, List.forall_mem_cons.2 ⟨subd10_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
