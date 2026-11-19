import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_32 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [0, 3] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [0, 4] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [1, -5] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [1, -4] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [1, 3] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [1, 4] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [2, -5] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [2, -4] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [2, -3] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [2, -2] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [2, -1] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [2, 0] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [2, 1] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [2, 3] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [3, -5] = true := by decide +kernel
theorem subd10_3_58 : subd10_3 [3, -4] = true := by decide +kernel
theorem subd10_3_59 : subd10_3 [3, -3] = true := by decide +kernel
theorem subd10_3_60 : subd10_3 [3, -2] = true := by decide +kernel
theorem subd10_3_61 : subd10_3 [3, -1] = true := by decide +kernel
theorem subd10_3_62 : subd10_3 [3, 0] = true := by decide +kernel
theorem subd10_3_63 : subd10_3 [3, 1] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_cons.2 ⟨subd10_3_58, List.forall_mem_cons.2 ⟨subd10_3_59, List.forall_mem_cons.2 ⟨subd10_3_60, List.forall_mem_cons.2 ⟨subd10_3_61, List.forall_mem_cons.2 ⟨subd10_3_62, List.forall_mem_cons.2 ⟨subd10_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_64 : subd10_3 [3, 2] = true := by decide +kernel
theorem subd10_3_65 : subd10_3 [4] = true := by decide +kernel
theorem sbd10_3_2 : ∀ q ∈ blkd10_3_2, subd10_3 q = true := by
  unfold blkd10_3_2
  exact List.forall_mem_cons.2 ⟨subd10_3_64, List.forall_mem_cons.2 ⟨subd10_3_65, List.forall_mem_nil _⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-3] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-2, -4] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-2, -3] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-2, -2] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-2, -1] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-2, 0] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-2, 1] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-2, 2] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-1, -4] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [-1, -1, -8] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [-1, -1, -7] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [-1, -1, -6] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [-1, -1, -5] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [-1, -1, -4] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [-1, -1, -3] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [-1, -1, -2] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [-1, -1, -1] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [-1, -1, 0] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [-1, -1, 1] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [-1, -1, 2] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [-1, -1, 3] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [-1, -1, 4] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [-1, -1, 5] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [-1, -1, 6] = true := by decide +kernel
theorem subd10_4_26 : subd10_4 [-1, 0, -8] = true := by decide +kernel
theorem subd10_4_27 : subd10_4 [-1, 0, -7] = true := by decide +kernel
theorem subd10_4_28 : subd10_4 [-1, 0, -6] = true := by decide +kernel
theorem subd10_4_29 : subd10_4 [-1, 0, -5] = true := by decide +kernel
theorem subd10_4_30 : subd10_4 [-1, 0, -4] = true := by decide +kernel
theorem subd10_4_31 : subd10_4 [-1, 0, -3] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_cons.2 ⟨subd10_4_26, List.forall_mem_cons.2 ⟨subd10_4_27, List.forall_mem_cons.2 ⟨subd10_4_28, List.forall_mem_cons.2 ⟨subd10_4_29, List.forall_mem_cons.2 ⟨subd10_4_30, List.forall_mem_cons.2 ⟨subd10_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_32 : subd10_4 [-1, 0, -2] = true := by decide +kernel
theorem subd10_4_33 : subd10_4 [-1, 0, -1] = true := by decide +kernel
theorem subd10_4_34 : subd10_4 [-1, 0, 0] = true := by decide +kernel
theorem subd10_4_35 : subd10_4 [-1, 0, 1] = true := by decide +kernel
theorem subd10_4_36 : subd10_4 [-1, 0, 2] = true := by decide +kernel
theorem subd10_4_37 : subd10_4 [-1, 0, 3] = true := by decide +kernel
theorem subd10_4_38 : subd10_4 [-1, 0, 4] = true := by decide +kernel
theorem subd10_4_39 : subd10_4 [-1, 0, 5] = true := by decide +kernel
theorem subd10_4_40 : subd10_4 [-1, 0, 6] = true := by decide +kernel
theorem subd10_4_41 : subd10_4 [-1, 0, 7] = true := by decide +kernel
theorem subd10_4_42 : subd10_4 [-1, 1, -8] = true := by decide +kernel
theorem subd10_4_43 : subd10_4 [-1, 1, -7] = true := by decide +kernel
theorem subd10_4_44 : subd10_4 [-1, 1, -6] = true := by decide +kernel
theorem subd10_4_45 : subd10_4 [-1, 1, -5] = true := by decide +kernel
theorem subd10_4_46 : subd10_4 [-1, 1, -4] = true := by decide +kernel
theorem subd10_4_47 : subd10_4 [-1, 1, -3] = true := by decide +kernel
theorem subd10_4_48 : subd10_4 [-1, 1, -2] = true := by decide +kernel
theorem subd10_4_49 : subd10_4 [-1, 1, -1] = true := by decide +kernel
theorem subd10_4_50 : subd10_4 [-1, 1, 0] = true := by decide +kernel
theorem subd10_4_51 : subd10_4 [-1, 1, 1] = true := by decide +kernel
theorem subd10_4_52 : subd10_4 [-1, 1, 2] = true := by decide +kernel
theorem subd10_4_53 : subd10_4 [-1, 1, 3] = true := by decide +kernel
theorem subd10_4_54 : subd10_4 [-1, 1, 4] = true := by decide +kernel
theorem subd10_4_55 : subd10_4 [-1, 1, 5] = true := by decide +kernel
theorem subd10_4_56 : subd10_4 [-1, 1, 6] = true := by decide +kernel
theorem subd10_4_57 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_58 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_59 : subd10_4 [0, -4] = true := by decide +kernel
theorem subd10_4_60 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_61 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_62 : subd10_4 [0, -1, -8] = true := by decide +kernel
theorem subd10_4_63 : subd10_4 [0, -1, -7] = true := by decide +kernel
theorem sbd10_4_1 : ∀ q ∈ blkd10_4_1, subd10_4 q = true := by
  unfold blkd10_4_1
  exact List.forall_mem_cons.2 ⟨subd10_4_32, List.forall_mem_cons.2 ⟨subd10_4_33, List.forall_mem_cons.2 ⟨subd10_4_34, List.forall_mem_cons.2 ⟨subd10_4_35, List.forall_mem_cons.2 ⟨subd10_4_36, List.forall_mem_cons.2 ⟨subd10_4_37, List.forall_mem_cons.2 ⟨subd10_4_38, List.forall_mem_cons.2 ⟨subd10_4_39, List.forall_mem_cons.2 ⟨subd10_4_40, List.forall_mem_cons.2 ⟨subd10_4_41, List.forall_mem_cons.2 ⟨subd10_4_42, List.forall_mem_cons.2 ⟨subd10_4_43, List.forall_mem_cons.2 ⟨subd10_4_44, List.forall_mem_cons.2 ⟨subd10_4_45, List.forall_mem_cons.2 ⟨subd10_4_46, List.forall_mem_cons.2 ⟨subd10_4_47, List.forall_mem_cons.2 ⟨subd10_4_48, List.forall_mem_cons.2 ⟨subd10_4_49, List.forall_mem_cons.2 ⟨subd10_4_50, List.forall_mem_cons.2 ⟨subd10_4_51, List.forall_mem_cons.2 ⟨subd10_4_52, List.forall_mem_cons.2 ⟨subd10_4_53, List.forall_mem_cons.2 ⟨subd10_4_54, List.forall_mem_cons.2 ⟨subd10_4_55, List.forall_mem_cons.2 ⟨subd10_4_56, List.forall_mem_cons.2 ⟨subd10_4_57, List.forall_mem_cons.2 ⟨subd10_4_58, List.forall_mem_cons.2 ⟨subd10_4_59, List.forall_mem_cons.2 ⟨subd10_4_60, List.forall_mem_cons.2 ⟨subd10_4_61, List.forall_mem_cons.2 ⟨subd10_4_62, List.forall_mem_cons.2 ⟨subd10_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_64 : subd10_4 [0, -1, -6] = true := by decide +kernel
theorem subd10_4_65 : subd10_4 [0, -1, -5] = true := by decide +kernel
theorem subd10_4_66 : subd10_4 [0, -1, -4] = true := by decide +kernel
theorem subd10_4_67 : subd10_4 [0, -1, -3] = true := by decide +kernel
theorem subd10_4_68 : subd10_4 [0, -1, -2] = true := by decide +kernel
theorem subd10_4_69 : subd10_4 [0, -1, -1] = true := by decide +kernel
theorem subd10_4_70 : subd10_4 [0, -1, 0] = true := by decide +kernel
theorem subd10_4_71 : subd10_4 [0, -1, 1] = true := by decide +kernel
theorem subd10_4_72 : subd10_4 [0, -1, 2] = true := by decide +kernel
theorem subd10_4_73 : subd10_4 [0, -1, 3] = true := by decide +kernel
theorem subd10_4_74 : subd10_4 [0, -1, 4] = true := by decide +kernel
theorem subd10_4_75 : subd10_4 [0, -1, 5] = true := by decide +kernel
theorem subd10_4_76 : subd10_4 [0, -1, 6] = true := by decide +kernel
theorem subd10_4_77 : subd10_4 [0, -1, 7] = true := by decide +kernel
theorem subd10_4_78 : subd10_4 [0, 0, -8] = true := by decide +kernel
theorem subd10_4_79 : subd10_4 [0, 0, -7] = true := by decide +kernel
theorem subd10_4_80 : subd10_4 [0, 0, -6] = true := by decide +kernel
theorem subd10_4_81 : subd10_4 [0, 0, -5] = true := by decide +kernel
theorem subd10_4_82 : subd10_4 [0, 0, -4] = true := by decide +kernel
theorem subd10_4_83 : subd10_4 [0, 0, -3] = true := by decide +kernel
theorem subd10_4_84 : subd10_4 [0, 0, -2] = true := by decide +kernel
theorem subd10_4_85 : subd10_4 [0, 0, -1] = true := by decide +kernel
theorem subd10_4_86 : subd10_4 [0, 0, 0] = true := by decide +kernel
theorem subd10_4_87 : subd10_4 [0, 0, 1] = true := by decide +kernel
theorem subd10_4_88 : subd10_4 [0, 0, 2] = true := by decide +kernel
theorem subd10_4_89 : subd10_4 [0, 0, 3] = true := by decide +kernel
theorem subd10_4_90 : subd10_4 [0, 0, 4] = true := by decide +kernel
theorem subd10_4_91 : subd10_4 [0, 0, 5] = true := by decide +kernel
theorem subd10_4_92 : subd10_4 [0, 0, 6] = true := by decide +kernel
theorem subd10_4_93 : subd10_4 [0, 0, 7] = true := by decide +kernel
theorem subd10_4_94 : subd10_4 [0, 1, -8] = true := by decide +kernel
theorem subd10_4_95 : subd10_4 [0, 1, -7] = true := by decide +kernel
theorem sbd10_4_2 : ∀ q ∈ blkd10_4_2, subd10_4 q = true := by
  unfold blkd10_4_2
  exact List.forall_mem_cons.2 ⟨subd10_4_64, List.forall_mem_cons.2 ⟨subd10_4_65, List.forall_mem_cons.2 ⟨subd10_4_66, List.forall_mem_cons.2 ⟨subd10_4_67, List.forall_mem_cons.2 ⟨subd10_4_68, List.forall_mem_cons.2 ⟨subd10_4_69, List.forall_mem_cons.2 ⟨subd10_4_70, List.forall_mem_cons.2 ⟨subd10_4_71, List.forall_mem_cons.2 ⟨subd10_4_72, List.forall_mem_cons.2 ⟨subd10_4_73, List.forall_mem_cons.2 ⟨subd10_4_74, List.forall_mem_cons.2 ⟨subd10_4_75, List.forall_mem_cons.2 ⟨subd10_4_76, List.forall_mem_cons.2 ⟨subd10_4_77, List.forall_mem_cons.2 ⟨subd10_4_78, List.forall_mem_cons.2 ⟨subd10_4_79, List.forall_mem_cons.2 ⟨subd10_4_80, List.forall_mem_cons.2 ⟨subd10_4_81, List.forall_mem_cons.2 ⟨subd10_4_82, List.forall_mem_cons.2 ⟨subd10_4_83, List.forall_mem_cons.2 ⟨subd10_4_84, List.forall_mem_cons.2 ⟨subd10_4_85, List.forall_mem_cons.2 ⟨subd10_4_86, List.forall_mem_cons.2 ⟨subd10_4_87, List.forall_mem_cons.2 ⟨subd10_4_88, List.forall_mem_cons.2 ⟨subd10_4_89, List.forall_mem_cons.2 ⟨subd10_4_90, List.forall_mem_cons.2 ⟨subd10_4_91, List.forall_mem_cons.2 ⟨subd10_4_92, List.forall_mem_cons.2 ⟨subd10_4_93, List.forall_mem_cons.2 ⟨subd10_4_94, List.forall_mem_cons.2 ⟨subd10_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_96 : subd10_4 [0, 1, -6] = true := by decide +kernel
theorem subd10_4_97 : subd10_4 [0, 1, -5] = true := by decide +kernel
theorem subd10_4_98 : subd10_4 [0, 1, -4] = true := by decide +kernel
theorem subd10_4_99 : subd10_4 [0, 1, -3] = true := by decide +kernel
theorem subd10_4_100 : subd10_4 [0, 1, -2] = true := by decide +kernel
theorem subd10_4_101 : subd10_4 [0, 1, -1] = true := by decide +kernel
theorem subd10_4_102 : subd10_4 [0, 1, 0] = true := by decide +kernel
theorem subd10_4_103 : subd10_4 [0, 1, 1] = true := by decide +kernel
theorem subd10_4_104 : subd10_4 [0, 1, 2] = true := by decide +kernel
theorem subd10_4_105 : subd10_4 [0, 1, 3] = true := by decide +kernel
theorem subd10_4_106 : subd10_4 [0, 1, 4] = true := by decide +kernel
theorem subd10_4_107 : subd10_4 [0, 1, 5] = true := by decide +kernel
theorem subd10_4_108 : subd10_4 [0, 1, 6] = true := by decide +kernel
theorem subd10_4_109 : subd10_4 [0, 1, 7] = true := by decide +kernel
theorem subd10_4_110 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_111 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_112 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_113 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_114 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_115 : subd10_4 [1, -1, -7] = true := by decide +kernel
theorem subd10_4_116 : subd10_4 [1, -1, -6] = true := by decide +kernel
theorem subd10_4_117 : subd10_4 [1, -1, -5] = true := by decide +kernel
theorem subd10_4_118 : subd10_4 [1, -1, -4] = true := by decide +kernel
theorem subd10_4_119 : subd10_4 [1, -1, -3] = true := by decide +kernel
theorem subd10_4_120 : subd10_4 [1, -1, -2] = true := by decide +kernel
theorem subd10_4_121 : subd10_4 [1, -1, -1] = true := by decide +kernel
theorem subd10_4_122 : subd10_4 [1, -1, 0] = true := by decide +kernel
theorem subd10_4_123 : subd10_4 [1, -1, 1] = true := by decide +kernel
theorem subd10_4_124 : subd10_4 [1, -1, 2] = true := by decide +kernel
theorem subd10_4_125 : subd10_4 [1, -1, 3] = true := by decide +kernel
theorem subd10_4_126 : subd10_4 [1, -1, 4] = true := by decide +kernel
theorem subd10_4_127 : subd10_4 [1, -1, 5] = true := by decide +kernel
theorem sbd10_4_3 : ∀ q ∈ blkd10_4_3, subd10_4 q = true := by
  unfold blkd10_4_3
  exact List.forall_mem_cons.2 ⟨subd10_4_96, List.forall_mem_cons.2 ⟨subd10_4_97, List.forall_mem_cons.2 ⟨subd10_4_98, List.forall_mem_cons.2 ⟨subd10_4_99, List.forall_mem_cons.2 ⟨subd10_4_100, List.forall_mem_cons.2 ⟨subd10_4_101, List.forall_mem_cons.2 ⟨subd10_4_102, List.forall_mem_cons.2 ⟨subd10_4_103, List.forall_mem_cons.2 ⟨subd10_4_104, List.forall_mem_cons.2 ⟨subd10_4_105, List.forall_mem_cons.2 ⟨subd10_4_106, List.forall_mem_cons.2 ⟨subd10_4_107, List.forall_mem_cons.2 ⟨subd10_4_108, List.forall_mem_cons.2 ⟨subd10_4_109, List.forall_mem_cons.2 ⟨subd10_4_110, List.forall_mem_cons.2 ⟨subd10_4_111, List.forall_mem_cons.2 ⟨subd10_4_112, List.forall_mem_cons.2 ⟨subd10_4_113, List.forall_mem_cons.2 ⟨subd10_4_114, List.forall_mem_cons.2 ⟨subd10_4_115, List.forall_mem_cons.2 ⟨subd10_4_116, List.forall_mem_cons.2 ⟨subd10_4_117, List.forall_mem_cons.2 ⟨subd10_4_118, List.forall_mem_cons.2 ⟨subd10_4_119, List.forall_mem_cons.2 ⟨subd10_4_120, List.forall_mem_cons.2 ⟨subd10_4_121, List.forall_mem_cons.2 ⟨subd10_4_122, List.forall_mem_cons.2 ⟨subd10_4_123, List.forall_mem_cons.2 ⟨subd10_4_124, List.forall_mem_cons.2 ⟨subd10_4_125, List.forall_mem_cons.2 ⟨subd10_4_126, List.forall_mem_cons.2 ⟨subd10_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_128 : subd10_4 [1, -1, 6] = true := by decide +kernel
theorem subd10_4_129 : subd10_4 [1, -1, 7] = true := by decide +kernel
theorem subd10_4_130 : subd10_4 [1, 0, -8] = true := by decide +kernel
theorem subd10_4_131 : subd10_4 [1, 0, -7] = true := by decide +kernel
theorem subd10_4_132 : subd10_4 [1, 0, -6] = true := by decide +kernel
theorem subd10_4_133 : subd10_4 [1, 0, -5] = true := by decide +kernel
theorem subd10_4_134 : subd10_4 [1, 0, -4] = true := by decide +kernel
theorem subd10_4_135 : subd10_4 [1, 0, -3] = true := by decide +kernel
theorem subd10_4_136 : subd10_4 [1, 0, -2] = true := by decide +kernel
theorem subd10_4_137 : subd10_4 [1, 0, -1] = true := by decide +kernel
theorem subd10_4_138 : subd10_4 [1, 0, 0] = true := by decide +kernel
theorem subd10_4_139 : subd10_4 [1, 0, 1] = true := by decide +kernel
theorem subd10_4_140 : subd10_4 [1, 0, 2] = true := by decide +kernel
theorem subd10_4_141 : subd10_4 [1, 0, 3] = true := by decide +kernel
theorem subd10_4_142 : subd10_4 [1, 0, 4] = true := by decide +kernel
theorem subd10_4_143 : subd10_4 [1, 0, 5] = true := by decide +kernel
theorem subd10_4_144 : subd10_4 [1, 0, 6] = true := by decide +kernel
theorem subd10_4_145 : subd10_4 [1, 0, 7] = true := by decide +kernel
theorem subd10_4_146 : subd10_4 [1, 1, -7] = true := by decide +kernel
theorem subd10_4_147 : subd10_4 [1, 1, -6] = true := by decide +kernel
theorem subd10_4_148 : subd10_4 [1, 1, -5] = true := by decide +kernel
theorem subd10_4_149 : subd10_4 [1, 1, -4] = true := by decide +kernel
theorem subd10_4_150 : subd10_4 [1, 1, -3] = true := by decide +kernel
theorem subd10_4_151 : subd10_4 [1, 1, -2] = true := by decide +kernel
theorem subd10_4_152 : subd10_4 [1, 1, -1] = true := by decide +kernel
theorem subd10_4_153 : subd10_4 [1, 1, 0] = true := by decide +kernel
theorem subd10_4_154 : subd10_4 [1, 1, 1] = true := by decide +kernel
theorem subd10_4_155 : subd10_4 [1, 1, 2] = true := by decide +kernel
theorem subd10_4_156 : subd10_4 [1, 1, 3] = true := by decide +kernel
theorem subd10_4_157 : subd10_4 [1, 1, 4] = true := by decide +kernel
theorem subd10_4_158 : subd10_4 [1, 1, 5] = true := by decide +kernel
theorem subd10_4_159 : subd10_4 [1, 1, 6] = true := by decide +kernel
theorem sbd10_4_4 : ∀ q ∈ blkd10_4_4, subd10_4 q = true := by
  unfold blkd10_4_4
  exact List.forall_mem_cons.2 ⟨subd10_4_128, List.forall_mem_cons.2 ⟨subd10_4_129, List.forall_mem_cons.2 ⟨subd10_4_130, List.forall_mem_cons.2 ⟨subd10_4_131, List.forall_mem_cons.2 ⟨subd10_4_132, List.forall_mem_cons.2 ⟨subd10_4_133, List.forall_mem_cons.2 ⟨subd10_4_134, List.forall_mem_cons.2 ⟨subd10_4_135, List.forall_mem_cons.2 ⟨subd10_4_136, List.forall_mem_cons.2 ⟨subd10_4_137, List.forall_mem_cons.2 ⟨subd10_4_138, List.forall_mem_cons.2 ⟨subd10_4_139, List.forall_mem_cons.2 ⟨subd10_4_140, List.forall_mem_cons.2 ⟨subd10_4_141, List.forall_mem_cons.2 ⟨subd10_4_142, List.forall_mem_cons.2 ⟨subd10_4_143, List.forall_mem_cons.2 ⟨subd10_4_144, List.forall_mem_cons.2 ⟨subd10_4_145, List.forall_mem_cons.2 ⟨subd10_4_146, List.forall_mem_cons.2 ⟨subd10_4_147, List.forall_mem_cons.2 ⟨subd10_4_148, List.forall_mem_cons.2 ⟨subd10_4_149, List.forall_mem_cons.2 ⟨subd10_4_150, List.forall_mem_cons.2 ⟨subd10_4_151, List.forall_mem_cons.2 ⟨subd10_4_152, List.forall_mem_cons.2 ⟨subd10_4_153, List.forall_mem_cons.2 ⟨subd10_4_154, List.forall_mem_cons.2 ⟨subd10_4_155, List.forall_mem_cons.2 ⟨subd10_4_156, List.forall_mem_cons.2 ⟨subd10_4_157, List.forall_mem_cons.2 ⟨subd10_4_158, List.forall_mem_cons.2 ⟨subd10_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_160 : subd10_4 [1, 1, 7] = true := by decide +kernel
theorem subd10_4_161 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_162 : subd10_4 [1, 3] = true := by decide +kernel
theorem subd10_4_163 : subd10_4 [2, -3] = true := by decide +kernel
theorem subd10_4_164 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_165 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_166 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_167 : subd10_4 [2, 1] = true := by decide +kernel
theorem subd10_4_168 : subd10_4 [2, 2] = true := by decide +kernel
theorem subd10_4_169 : subd10_4 [2, 3] = true := by decide +kernel
theorem subd10_4_170 : subd10_4 [3] = true := by decide +kernel
theorem sbd10_4_5 : ∀ q ∈ blkd10_4_5, subd10_4 q = true := by
  unfold blkd10_4_5
  exact List.forall_mem_cons.2 ⟨subd10_4_160, List.forall_mem_cons.2 ⟨subd10_4_161, List.forall_mem_cons.2 ⟨subd10_4_162, List.forall_mem_cons.2 ⟨subd10_4_163, List.forall_mem_cons.2 ⟨subd10_4_164, List.forall_mem_cons.2 ⟨subd10_4_165, List.forall_mem_cons.2 ⟨subd10_4_166, List.forall_mem_cons.2 ⟨subd10_4_167, List.forall_mem_cons.2 ⟨subd10_4_168, List.forall_mem_cons.2 ⟨subd10_4_169, List.forall_mem_cons.2 ⟨subd10_4_170, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
