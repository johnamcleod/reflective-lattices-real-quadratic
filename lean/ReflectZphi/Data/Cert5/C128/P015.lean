import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_4_64 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_65 : subd4_4 [1, 0] = true := by decide +kernel
theorem subd4_4_66 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_67 : subd4_4 [1, 2] = true := by decide +kernel
theorem subd4_4_68 : subd4_4 [1, 3] = true := by decide +kernel
theorem subd4_4_69 : subd4_4 [1, 4] = true := by decide +kernel
theorem subd4_4_70 : subd4_4 [1, 5] = true := by decide +kernel
theorem subd4_4_71 : subd4_4 [2, -6] = true := by decide +kernel
theorem subd4_4_72 : subd4_4 [2, -5] = true := by decide +kernel
theorem subd4_4_73 : subd4_4 [2, -4] = true := by decide +kernel
theorem subd4_4_74 : subd4_4 [2, -3] = true := by decide +kernel
theorem subd4_4_75 : subd4_4 [2, -2] = true := by decide +kernel
theorem subd4_4_76 : subd4_4 [2, -1] = true := by decide +kernel
theorem subd4_4_77 : subd4_4 [2, 0] = true := by decide +kernel
theorem subd4_4_78 : subd4_4 [2, 1] = true := by decide +kernel
theorem subd4_4_79 : subd4_4 [2, 2] = true := by decide +kernel
theorem subd4_4_80 : subd4_4 [2, 3] = true := by decide +kernel
theorem subd4_4_81 : subd4_4 [2, 4] = true := by decide +kernel
theorem subd4_4_82 : subd4_4 [2, 5] = true := by decide +kernel
theorem subd4_4_83 : subd4_4 [3, -6] = true := by decide +kernel
theorem subd4_4_84 : subd4_4 [3, -5] = true := by decide +kernel
theorem subd4_4_85 : subd4_4 [3, -4] = true := by decide +kernel
theorem subd4_4_86 : subd4_4 [3, -3] = true := by decide +kernel
theorem subd4_4_87 : subd4_4 [3, -2] = true := by decide +kernel
theorem subd4_4_88 : subd4_4 [3, -1] = true := by decide +kernel
theorem subd4_4_89 : subd4_4 [3, 0] = true := by decide +kernel
theorem subd4_4_90 : subd4_4 [3, 1] = true := by decide +kernel
theorem subd4_4_91 : subd4_4 [3, 2] = true := by decide +kernel
theorem subd4_4_92 : subd4_4 [3, 3] = true := by decide +kernel
theorem subd4_4_93 : subd4_4 [3, 4] = true := by decide +kernel
theorem subd4_4_94 : subd4_4 [4, -5] = true := by decide +kernel
theorem subd4_4_95 : subd4_4 [4, -4] = true := by decide +kernel
theorem sbd4_4_2 : ∀ q ∈ blkd4_4_2, subd4_4 q = true := by
  unfold blkd4_4_2
  exact List.forall_mem_cons.2 ⟨subd4_4_64, List.forall_mem_cons.2 ⟨subd4_4_65, List.forall_mem_cons.2 ⟨subd4_4_66, List.forall_mem_cons.2 ⟨subd4_4_67, List.forall_mem_cons.2 ⟨subd4_4_68, List.forall_mem_cons.2 ⟨subd4_4_69, List.forall_mem_cons.2 ⟨subd4_4_70, List.forall_mem_cons.2 ⟨subd4_4_71, List.forall_mem_cons.2 ⟨subd4_4_72, List.forall_mem_cons.2 ⟨subd4_4_73, List.forall_mem_cons.2 ⟨subd4_4_74, List.forall_mem_cons.2 ⟨subd4_4_75, List.forall_mem_cons.2 ⟨subd4_4_76, List.forall_mem_cons.2 ⟨subd4_4_77, List.forall_mem_cons.2 ⟨subd4_4_78, List.forall_mem_cons.2 ⟨subd4_4_79, List.forall_mem_cons.2 ⟨subd4_4_80, List.forall_mem_cons.2 ⟨subd4_4_81, List.forall_mem_cons.2 ⟨subd4_4_82, List.forall_mem_cons.2 ⟨subd4_4_83, List.forall_mem_cons.2 ⟨subd4_4_84, List.forall_mem_cons.2 ⟨subd4_4_85, List.forall_mem_cons.2 ⟨subd4_4_86, List.forall_mem_cons.2 ⟨subd4_4_87, List.forall_mem_cons.2 ⟨subd4_4_88, List.forall_mem_cons.2 ⟨subd4_4_89, List.forall_mem_cons.2 ⟨subd4_4_90, List.forall_mem_cons.2 ⟨subd4_4_91, List.forall_mem_cons.2 ⟨subd4_4_92, List.forall_mem_cons.2 ⟨subd4_4_93, List.forall_mem_cons.2 ⟨subd4_4_94, List.forall_mem_cons.2 ⟨subd4_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_96 : subd4_4 [4, -3] = true := by decide +kernel
theorem subd4_4_97 : subd4_4 [4, -2] = true := by decide +kernel
theorem subd4_4_98 : subd4_4 [4, -1] = true := by decide +kernel
theorem subd4_4_99 : subd4_4 [4, 0] = true := by decide +kernel
theorem subd4_4_100 : subd4_4 [4, 1] = true := by decide +kernel
theorem subd4_4_101 : subd4_4 [4, 2] = true := by decide +kernel
theorem subd4_4_102 : subd4_4 [4, 3] = true := by decide +kernel
theorem subd4_4_103 : subd4_4 [5] = true := by decide +kernel
theorem sbd4_4_3 : ∀ q ∈ blkd4_4_3, subd4_4 q = true := by
  unfold blkd4_4_3
  exact List.forall_mem_cons.2 ⟨subd4_4_96, List.forall_mem_cons.2 ⟨subd4_4_97, List.forall_mem_cons.2 ⟨subd4_4_98, List.forall_mem_cons.2 ⟨subd4_4_99, List.forall_mem_cons.2 ⟨subd4_4_100, List.forall_mem_cons.2 ⟨subd4_4_101, List.forall_mem_cons.2 ⟨subd4_4_102, List.forall_mem_cons.2 ⟨subd4_4_103, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [-3] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-2, -3] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [-2, -2] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [-2, -1, -11] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [-2, -1, -10] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [-2, -1, -9] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [-2, -1, -8] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [-2, -1, -7] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [-2, -1, -6] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [-2, -1, -5] = true := by decide +kernel
theorem subd4_5_10 : subd4_5 [-2, -1, -4] = true := by decide +kernel
theorem subd4_5_11 : subd4_5 [-2, -1, -3] = true := by decide +kernel
theorem subd4_5_12 : subd4_5 [-2, -1, -2] = true := by decide +kernel
theorem subd4_5_13 : subd4_5 [-2, -1, -1] = true := by decide +kernel
theorem subd4_5_14 : subd4_5 [-2, -1, 0] = true := by decide +kernel
theorem subd4_5_15 : subd4_5 [-2, -1, 1] = true := by decide +kernel
theorem subd4_5_16 : subd4_5 [-2, -1, 2] = true := by decide +kernel
theorem subd4_5_17 : subd4_5 [-2, -1, 3] = true := by decide +kernel
theorem subd4_5_18 : subd4_5 [-2, -1, 4] = true := by decide +kernel
theorem subd4_5_19 : subd4_5 [-2, -1, 5] = true := by decide +kernel
theorem subd4_5_20 : subd4_5 [-2, -1, 6] = true := by decide +kernel
theorem subd4_5_21 : subd4_5 [-2, -1, 7] = true := by decide +kernel
theorem subd4_5_22 : subd4_5 [-2, -1, 8] = true := by decide +kernel
theorem subd4_5_23 : subd4_5 [-2, 0, -11] = true := by decide +kernel
theorem subd4_5_24 : subd4_5 [-2, 0, -10] = true := by decide +kernel
theorem subd4_5_25 : subd4_5 [-2, 0, -9] = true := by decide +kernel
theorem subd4_5_26 : subd4_5 [-2, 0, -8] = true := by decide +kernel
theorem subd4_5_27 : subd4_5 [-2, 0, -7] = true := by decide +kernel
theorem subd4_5_28 : subd4_5 [-2, 0, -6] = true := by decide +kernel
theorem subd4_5_29 : subd4_5 [-2, 0, -5] = true := by decide +kernel
theorem subd4_5_30 : subd4_5 [-2, 0, -4] = true := by decide +kernel
theorem subd4_5_31 : subd4_5 [-2, 0, -3] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_cons.2 ⟨subd4_5_10, List.forall_mem_cons.2 ⟨subd4_5_11, List.forall_mem_cons.2 ⟨subd4_5_12, List.forall_mem_cons.2 ⟨subd4_5_13, List.forall_mem_cons.2 ⟨subd4_5_14, List.forall_mem_cons.2 ⟨subd4_5_15, List.forall_mem_cons.2 ⟨subd4_5_16, List.forall_mem_cons.2 ⟨subd4_5_17, List.forall_mem_cons.2 ⟨subd4_5_18, List.forall_mem_cons.2 ⟨subd4_5_19, List.forall_mem_cons.2 ⟨subd4_5_20, List.forall_mem_cons.2 ⟨subd4_5_21, List.forall_mem_cons.2 ⟨subd4_5_22, List.forall_mem_cons.2 ⟨subd4_5_23, List.forall_mem_cons.2 ⟨subd4_5_24, List.forall_mem_cons.2 ⟨subd4_5_25, List.forall_mem_cons.2 ⟨subd4_5_26, List.forall_mem_cons.2 ⟨subd4_5_27, List.forall_mem_cons.2 ⟨subd4_5_28, List.forall_mem_cons.2 ⟨subd4_5_29, List.forall_mem_cons.2 ⟨subd4_5_30, List.forall_mem_cons.2 ⟨subd4_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_32 : subd4_5 [-2, 0, -2] = true := by decide +kernel
theorem subd4_5_33 : subd4_5 [-2, 0, -1] = true := by decide +kernel
theorem subd4_5_34 : subd4_5 [-2, 0, 0] = true := by decide +kernel
theorem subd4_5_35 : subd4_5 [-2, 0, 1] = true := by decide +kernel
theorem subd4_5_36 : subd4_5 [-2, 0, 2] = true := by decide +kernel
theorem subd4_5_37 : subd4_5 [-2, 0, 3] = true := by decide +kernel
theorem subd4_5_38 : subd4_5 [-2, 0, 4] = true := by decide +kernel
theorem subd4_5_39 : subd4_5 [-2, 0, 5] = true := by decide +kernel
theorem subd4_5_40 : subd4_5 [-2, 0, 6] = true := by decide +kernel
theorem subd4_5_41 : subd4_5 [-2, 0, 7] = true := by decide +kernel
theorem subd4_5_42 : subd4_5 [-2, 0, 8] = true := by decide +kernel
theorem subd4_5_43 : subd4_5 [-2, 1, -8] = true := by decide +kernel
theorem subd4_5_44 : subd4_5 [-2, 1, -7] = true := by decide +kernel
theorem subd4_5_45 : subd4_5 [-2, 1, -6] = true := by decide +kernel
theorem subd4_5_46 : subd4_5 [-2, 1, -5] = true := by decide +kernel
theorem subd4_5_47 : subd4_5 [-2, 1, -4] = true := by decide +kernel
theorem subd4_5_48 : subd4_5 [-2, 1, -3] = true := by decide +kernel
theorem subd4_5_49 : subd4_5 [-2, 1, -2] = true := by decide +kernel
theorem subd4_5_50 : subd4_5 [-2, 1, -1] = true := by decide +kernel
theorem subd4_5_51 : subd4_5 [-2, 1, 0] = true := by decide +kernel
theorem subd4_5_52 : subd4_5 [-2, 1, 1] = true := by decide +kernel
theorem subd4_5_53 : subd4_5 [-2, 1, 2] = true := by decide +kernel
theorem subd4_5_54 : subd4_5 [-2, 1, 3] = true := by decide +kernel
theorem subd4_5_55 : subd4_5 [-2, 1, 4] = true := by decide +kernel
theorem subd4_5_56 : subd4_5 [-2, 1, 5] = true := by decide +kernel
theorem subd4_5_57 : subd4_5 [-2, 1, 6] = true := by decide +kernel
theorem subd4_5_58 : subd4_5 [-1, -3] = true := by decide +kernel
theorem subd4_5_59 : subd4_5 [-1, -2, -9] = true := by decide +kernel
theorem subd4_5_60 : subd4_5 [-1, -2, -8] = true := by decide +kernel
theorem subd4_5_61 : subd4_5 [-1, -2, -7] = true := by decide +kernel
theorem subd4_5_62 : subd4_5 [-1, -2, -6] = true := by decide +kernel
theorem subd4_5_63 : subd4_5 [-1, -2, -5] = true := by decide +kernel
theorem sbd4_5_1 : ∀ q ∈ blkd4_5_1, subd4_5 q = true := by
  unfold blkd4_5_1
  exact List.forall_mem_cons.2 ⟨subd4_5_32, List.forall_mem_cons.2 ⟨subd4_5_33, List.forall_mem_cons.2 ⟨subd4_5_34, List.forall_mem_cons.2 ⟨subd4_5_35, List.forall_mem_cons.2 ⟨subd4_5_36, List.forall_mem_cons.2 ⟨subd4_5_37, List.forall_mem_cons.2 ⟨subd4_5_38, List.forall_mem_cons.2 ⟨subd4_5_39, List.forall_mem_cons.2 ⟨subd4_5_40, List.forall_mem_cons.2 ⟨subd4_5_41, List.forall_mem_cons.2 ⟨subd4_5_42, List.forall_mem_cons.2 ⟨subd4_5_43, List.forall_mem_cons.2 ⟨subd4_5_44, List.forall_mem_cons.2 ⟨subd4_5_45, List.forall_mem_cons.2 ⟨subd4_5_46, List.forall_mem_cons.2 ⟨subd4_5_47, List.forall_mem_cons.2 ⟨subd4_5_48, List.forall_mem_cons.2 ⟨subd4_5_49, List.forall_mem_cons.2 ⟨subd4_5_50, List.forall_mem_cons.2 ⟨subd4_5_51, List.forall_mem_cons.2 ⟨subd4_5_52, List.forall_mem_cons.2 ⟨subd4_5_53, List.forall_mem_cons.2 ⟨subd4_5_54, List.forall_mem_cons.2 ⟨subd4_5_55, List.forall_mem_cons.2 ⟨subd4_5_56, List.forall_mem_cons.2 ⟨subd4_5_57, List.forall_mem_cons.2 ⟨subd4_5_58, List.forall_mem_cons.2 ⟨subd4_5_59, List.forall_mem_cons.2 ⟨subd4_5_60, List.forall_mem_cons.2 ⟨subd4_5_61, List.forall_mem_cons.2 ⟨subd4_5_62, List.forall_mem_cons.2 ⟨subd4_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_64 : subd4_5 [-1, -2, -4] = true := by decide +kernel
theorem subd4_5_65 : subd4_5 [-1, -2, -3] = true := by decide +kernel
theorem subd4_5_66 : subd4_5 [-1, -2, -2] = true := by decide +kernel
theorem subd4_5_67 : subd4_5 [-1, -2, -1] = true := by decide +kernel
theorem subd4_5_68 : subd4_5 [-1, -2, 0] = true := by decide +kernel
theorem subd4_5_69 : subd4_5 [-1, -2, 1] = true := by decide +kernel
theorem subd4_5_70 : subd4_5 [-1, -2, 2] = true := by decide +kernel
theorem subd4_5_71 : subd4_5 [-1, -2, 3] = true := by decide +kernel
theorem subd4_5_72 : subd4_5 [-1, -2, 4] = true := by decide +kernel
theorem subd4_5_73 : subd4_5 [-1, -2, 5] = true := by decide +kernel
theorem subd4_5_74 : subd4_5 [-1, -2, 6] = true := by decide +kernel
theorem subd4_5_75 : subd4_5 [-1, -2, 7] = true := by decide +kernel
theorem subd4_5_76 : subd4_5 [-1, -1, -12] = true := by decide +kernel
theorem subd4_5_77 : subd4_5 [-1, -1, -11] = true := by decide +kernel
theorem subd4_5_78 : subd4_5 [-1, -1, -10] = true := by decide +kernel
theorem subd4_5_79 : subd4_5 [-1, -1, -9] = true := by decide +kernel
theorem subd4_5_80 : subd4_5 [-1, -1, -8] = true := by decide +kernel
theorem subd4_5_81 : subd4_5 [-1, -1, -7] = true := by decide +kernel
theorem subd4_5_82 : subd4_5 [-1, -1, -6] = true := by decide +kernel
theorem subd4_5_83 : subd4_5 [-1, -1, -5] = true := by decide +kernel
theorem subd4_5_84 : subd4_5 [-1, -1, -4] = true := by decide +kernel
theorem subd4_5_85 : subd4_5 [-1, -1, -3] = true := by decide +kernel
theorem subd4_5_86 : subd4_5 [-1, -1, -2] = true := by decide +kernel
theorem subd4_5_87 : subd4_5 [-1, -1, -1] = true := by decide +kernel
theorem subd4_5_88 : subd4_5 [-1, -1, 0] = true := by decide +kernel
theorem subd4_5_89 : subd4_5 [-1, -1, 1] = true := by decide +kernel
theorem subd4_5_90 : subd4_5 [-1, -1, 2] = true := by decide +kernel
theorem subd4_5_91 : subd4_5 [-1, -1, 3] = true := by decide +kernel
theorem subd4_5_92 : subd4_5 [-1, -1, 4] = true := by decide +kernel
theorem subd4_5_93 : subd4_5 [-1, -1, 5] = true := by decide +kernel
theorem subd4_5_94 : subd4_5 [-1, -1, 6] = true := by decide +kernel
theorem subd4_5_95 : subd4_5 [-1, -1, 7] = true := by decide +kernel
theorem sbd4_5_2 : ∀ q ∈ blkd4_5_2, subd4_5 q = true := by
  unfold blkd4_5_2
  exact List.forall_mem_cons.2 ⟨subd4_5_64, List.forall_mem_cons.2 ⟨subd4_5_65, List.forall_mem_cons.2 ⟨subd4_5_66, List.forall_mem_cons.2 ⟨subd4_5_67, List.forall_mem_cons.2 ⟨subd4_5_68, List.forall_mem_cons.2 ⟨subd4_5_69, List.forall_mem_cons.2 ⟨subd4_5_70, List.forall_mem_cons.2 ⟨subd4_5_71, List.forall_mem_cons.2 ⟨subd4_5_72, List.forall_mem_cons.2 ⟨subd4_5_73, List.forall_mem_cons.2 ⟨subd4_5_74, List.forall_mem_cons.2 ⟨subd4_5_75, List.forall_mem_cons.2 ⟨subd4_5_76, List.forall_mem_cons.2 ⟨subd4_5_77, List.forall_mem_cons.2 ⟨subd4_5_78, List.forall_mem_cons.2 ⟨subd4_5_79, List.forall_mem_cons.2 ⟨subd4_5_80, List.forall_mem_cons.2 ⟨subd4_5_81, List.forall_mem_cons.2 ⟨subd4_5_82, List.forall_mem_cons.2 ⟨subd4_5_83, List.forall_mem_cons.2 ⟨subd4_5_84, List.forall_mem_cons.2 ⟨subd4_5_85, List.forall_mem_cons.2 ⟨subd4_5_86, List.forall_mem_cons.2 ⟨subd4_5_87, List.forall_mem_cons.2 ⟨subd4_5_88, List.forall_mem_cons.2 ⟨subd4_5_89, List.forall_mem_cons.2 ⟨subd4_5_90, List.forall_mem_cons.2 ⟨subd4_5_91, List.forall_mem_cons.2 ⟨subd4_5_92, List.forall_mem_cons.2 ⟨subd4_5_93, List.forall_mem_cons.2 ⟨subd4_5_94, List.forall_mem_cons.2 ⟨subd4_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_96 : subd4_5 [-1, -1, 8] = true := by decide +kernel
theorem subd4_5_97 : subd4_5 [-1, -1, 9] = true := by decide +kernel
theorem subd4_5_98 : subd4_5 [-1, -1, 10] = true := by decide +kernel
theorem subd4_5_99 : subd4_5 [-1, 0, -12] = true := by decide +kernel
theorem subd4_5_100 : subd4_5 [-1, 0, -11] = true := by decide +kernel
theorem subd4_5_101 : subd4_5 [-1, 0, -10] = true := by decide +kernel
theorem subd4_5_102 : subd4_5 [-1, 0, -9] = true := by decide +kernel
theorem subd4_5_103 : subd4_5 [-1, 0, -8] = true := by decide +kernel
theorem subd4_5_104 : subd4_5 [-1, 0, -7] = true := by decide +kernel
theorem subd4_5_105 : subd4_5 [-1, 0, -6] = true := by decide +kernel
theorem subd4_5_106 : subd4_5 [-1, 0, -5] = true := by decide +kernel
theorem subd4_5_107 : subd4_5 [-1, 0, -4] = true := by decide +kernel
theorem subd4_5_108 : subd4_5 [-1, 0, -3] = true := by decide +kernel
theorem subd4_5_109 : subd4_5 [-1, 0, -2] = true := by decide +kernel
theorem subd4_5_110 : subd4_5 [-1, 0, -1] = true := by decide +kernel
theorem subd4_5_111 : subd4_5 [-1, 0, 0] = true := by decide +kernel
theorem subd4_5_112 : subd4_5 [-1, 0, 1] = true := by decide +kernel
theorem subd4_5_113 : subd4_5 [-1, 0, 2] = true := by decide +kernel
theorem subd4_5_114 : subd4_5 [-1, 0, 3] = true := by decide +kernel
theorem subd4_5_115 : subd4_5 [-1, 0, 4] = true := by decide +kernel
theorem subd4_5_116 : subd4_5 [-1, 0, 5] = true := by decide +kernel
theorem subd4_5_117 : subd4_5 [-1, 0, 6] = true := by decide +kernel
theorem subd4_5_118 : subd4_5 [-1, 0, 7] = true := by decide +kernel
theorem subd4_5_119 : subd4_5 [-1, 0, 8] = true := by decide +kernel
theorem subd4_5_120 : subd4_5 [-1, 0, 9] = true := by decide +kernel
theorem subd4_5_121 : subd4_5 [-1, 0, 10] = true := by decide +kernel
theorem subd4_5_122 : subd4_5 [-1, 1, -11] = true := by decide +kernel
theorem subd4_5_123 : subd4_5 [-1, 1, -10] = true := by decide +kernel
theorem subd4_5_124 : subd4_5 [-1, 1, -9] = true := by decide +kernel
theorem subd4_5_125 : subd4_5 [-1, 1, -8] = true := by decide +kernel
theorem subd4_5_126 : subd4_5 [-1, 1, -7] = true := by decide +kernel
theorem subd4_5_127 : subd4_5 [-1, 1, -6] = true := by decide +kernel
theorem sbd4_5_3 : ∀ q ∈ blkd4_5_3, subd4_5 q = true := by
  unfold blkd4_5_3
  exact List.forall_mem_cons.2 ⟨subd4_5_96, List.forall_mem_cons.2 ⟨subd4_5_97, List.forall_mem_cons.2 ⟨subd4_5_98, List.forall_mem_cons.2 ⟨subd4_5_99, List.forall_mem_cons.2 ⟨subd4_5_100, List.forall_mem_cons.2 ⟨subd4_5_101, List.forall_mem_cons.2 ⟨subd4_5_102, List.forall_mem_cons.2 ⟨subd4_5_103, List.forall_mem_cons.2 ⟨subd4_5_104, List.forall_mem_cons.2 ⟨subd4_5_105, List.forall_mem_cons.2 ⟨subd4_5_106, List.forall_mem_cons.2 ⟨subd4_5_107, List.forall_mem_cons.2 ⟨subd4_5_108, List.forall_mem_cons.2 ⟨subd4_5_109, List.forall_mem_cons.2 ⟨subd4_5_110, List.forall_mem_cons.2 ⟨subd4_5_111, List.forall_mem_cons.2 ⟨subd4_5_112, List.forall_mem_cons.2 ⟨subd4_5_113, List.forall_mem_cons.2 ⟨subd4_5_114, List.forall_mem_cons.2 ⟨subd4_5_115, List.forall_mem_cons.2 ⟨subd4_5_116, List.forall_mem_cons.2 ⟨subd4_5_117, List.forall_mem_cons.2 ⟨subd4_5_118, List.forall_mem_cons.2 ⟨subd4_5_119, List.forall_mem_cons.2 ⟨subd4_5_120, List.forall_mem_cons.2 ⟨subd4_5_121, List.forall_mem_cons.2 ⟨subd4_5_122, List.forall_mem_cons.2 ⟨subd4_5_123, List.forall_mem_cons.2 ⟨subd4_5_124, List.forall_mem_cons.2 ⟨subd4_5_125, List.forall_mem_cons.2 ⟨subd4_5_126, List.forall_mem_cons.2 ⟨subd4_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_128 : subd4_5 [-1, 1, -5] = true := by decide +kernel
theorem subd4_5_129 : subd4_5 [-1, 1, -4] = true := by decide +kernel
theorem subd4_5_130 : subd4_5 [-1, 1, -3] = true := by decide +kernel
theorem subd4_5_131 : subd4_5 [-1, 1, -2] = true := by decide +kernel
theorem subd4_5_132 : subd4_5 [-1, 1, -1] = true := by decide +kernel
theorem subd4_5_133 : subd4_5 [-1, 1, 0] = true := by decide +kernel
theorem subd4_5_134 : subd4_5 [-1, 1, 1] = true := by decide +kernel
theorem subd4_5_135 : subd4_5 [-1, 1, 2] = true := by decide +kernel
theorem subd4_5_136 : subd4_5 [-1, 1, 3] = true := by decide +kernel
theorem subd4_5_137 : subd4_5 [-1, 1, 4] = true := by decide +kernel
theorem subd4_5_138 : subd4_5 [-1, 1, 5] = true := by decide +kernel
theorem subd4_5_139 : subd4_5 [-1, 1, 6] = true := by decide +kernel
theorem subd4_5_140 : subd4_5 [-1, 1, 7] = true := by decide +kernel
theorem subd4_5_141 : subd4_5 [-1, 1, 8] = true := by decide +kernel
theorem subd4_5_142 : subd4_5 [-1, 1, 9] = true := by decide +kernel
theorem subd4_5_143 : subd4_5 [-1, 2] = true := by decide +kernel
theorem subd4_5_144 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_145 : subd4_5 [0, -2, -9] = true := by decide +kernel
theorem subd4_5_146 : subd4_5 [0, -2, -8] = true := by decide +kernel
theorem subd4_5_147 : subd4_5 [0, -2, -7] = true := by decide +kernel
theorem subd4_5_148 : subd4_5 [0, -2, -6] = true := by decide +kernel
theorem subd4_5_149 : subd4_5 [0, -2, -5] = true := by decide +kernel
theorem subd4_5_150 : subd4_5 [0, -2, -4] = true := by decide +kernel
theorem subd4_5_151 : subd4_5 [0, -2, -3] = true := by decide +kernel
theorem subd4_5_152 : subd4_5 [0, -2, -2] = true := by decide +kernel
theorem subd4_5_153 : subd4_5 [0, -2, -1] = true := by decide +kernel
theorem subd4_5_154 : subd4_5 [0, -2, 0] = true := by decide +kernel
theorem subd4_5_155 : subd4_5 [0, -2, 1] = true := by decide +kernel
theorem subd4_5_156 : subd4_5 [0, -2, 2] = true := by decide +kernel
theorem subd4_5_157 : subd4_5 [0, -2, 3] = true := by decide +kernel
theorem subd4_5_158 : subd4_5 [0, -2, 4] = true := by decide +kernel
theorem subd4_5_159 : subd4_5 [0, -2, 5] = true := by decide +kernel
theorem sbd4_5_4 : ∀ q ∈ blkd4_5_4, subd4_5 q = true := by
  unfold blkd4_5_4
  exact List.forall_mem_cons.2 ⟨subd4_5_128, List.forall_mem_cons.2 ⟨subd4_5_129, List.forall_mem_cons.2 ⟨subd4_5_130, List.forall_mem_cons.2 ⟨subd4_5_131, List.forall_mem_cons.2 ⟨subd4_5_132, List.forall_mem_cons.2 ⟨subd4_5_133, List.forall_mem_cons.2 ⟨subd4_5_134, List.forall_mem_cons.2 ⟨subd4_5_135, List.forall_mem_cons.2 ⟨subd4_5_136, List.forall_mem_cons.2 ⟨subd4_5_137, List.forall_mem_cons.2 ⟨subd4_5_138, List.forall_mem_cons.2 ⟨subd4_5_139, List.forall_mem_cons.2 ⟨subd4_5_140, List.forall_mem_cons.2 ⟨subd4_5_141, List.forall_mem_cons.2 ⟨subd4_5_142, List.forall_mem_cons.2 ⟨subd4_5_143, List.forall_mem_cons.2 ⟨subd4_5_144, List.forall_mem_cons.2 ⟨subd4_5_145, List.forall_mem_cons.2 ⟨subd4_5_146, List.forall_mem_cons.2 ⟨subd4_5_147, List.forall_mem_cons.2 ⟨subd4_5_148, List.forall_mem_cons.2 ⟨subd4_5_149, List.forall_mem_cons.2 ⟨subd4_5_150, List.forall_mem_cons.2 ⟨subd4_5_151, List.forall_mem_cons.2 ⟨subd4_5_152, List.forall_mem_cons.2 ⟨subd4_5_153, List.forall_mem_cons.2 ⟨subd4_5_154, List.forall_mem_cons.2 ⟨subd4_5_155, List.forall_mem_cons.2 ⟨subd4_5_156, List.forall_mem_cons.2 ⟨subd4_5_157, List.forall_mem_cons.2 ⟨subd4_5_158, List.forall_mem_cons.2 ⟨subd4_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_160 : subd4_5 [0, -2, 6] = true := by decide +kernel
theorem subd4_5_161 : subd4_5 [0, -2, 7] = true := by decide +kernel
theorem subd4_5_162 : subd4_5 [0, -2, 8] = true := by decide +kernel
theorem subd4_5_163 : subd4_5 [0, -1, -12] = true := by decide +kernel
theorem subd4_5_164 : subd4_5 [0, -1, -11] = true := by decide +kernel
theorem subd4_5_165 : subd4_5 [0, -1, -10] = true := by decide +kernel
theorem subd4_5_166 : subd4_5 [0, -1, -9] = true := by decide +kernel
theorem subd4_5_167 : subd4_5 [0, -1, -8] = true := by decide +kernel
theorem subd4_5_168 : subd4_5 [0, -1, -7] = true := by decide +kernel
theorem subd4_5_169 : subd4_5 [0, -1, -6] = true := by decide +kernel
theorem subd4_5_170 : subd4_5 [0, -1, -5] = true := by decide +kernel
theorem subd4_5_171 : subd4_5 [0, -1, -4] = true := by decide +kernel
theorem subd4_5_172 : subd4_5 [0, -1, -3] = true := by decide +kernel
theorem subd4_5_173 : subd4_5 [0, -1, -2] = true := by decide +kernel
theorem subd4_5_174 : subd4_5 [0, -1, -1] = true := by decide +kernel
theorem subd4_5_175 : subd4_5 [0, -1, 0] = true := by decide +kernel
theorem subd4_5_176 : subd4_5 [0, -1, 1] = true := by decide +kernel
theorem subd4_5_177 : subd4_5 [0, -1, 2] = true := by decide +kernel
theorem subd4_5_178 : subd4_5 [0, -1, 3] = true := by decide +kernel
theorem subd4_5_179 : subd4_5 [0, -1, 4] = true := by decide +kernel
theorem subd4_5_180 : subd4_5 [0, -1, 5] = true := by decide +kernel
theorem subd4_5_181 : subd4_5 [0, -1, 6] = true := by decide +kernel
theorem subd4_5_182 : subd4_5 [0, -1, 7] = true := by decide +kernel
theorem subd4_5_183 : subd4_5 [0, -1, 8] = true := by decide +kernel
theorem subd4_5_184 : subd4_5 [0, -1, 9] = true := by decide +kernel
theorem subd4_5_185 : subd4_5 [0, -1, 10] = true := by decide +kernel
theorem subd4_5_186 : subd4_5 [0, -1, 11] = true := by decide +kernel
theorem subd4_5_187 : subd4_5 [0, 0, -12] = true := by decide +kernel
theorem subd4_5_188 : subd4_5 [0, 0, -11] = true := by decide +kernel
theorem subd4_5_189 : subd4_5 [0, 0, -10] = true := by decide +kernel
theorem subd4_5_190 : subd4_5 [0, 0, -9] = true := by decide +kernel
theorem subd4_5_191 : subd4_5 [0, 0, -8] = true := by decide +kernel
theorem sbd4_5_5 : ∀ q ∈ blkd4_5_5, subd4_5 q = true := by
  unfold blkd4_5_5
  exact List.forall_mem_cons.2 ⟨subd4_5_160, List.forall_mem_cons.2 ⟨subd4_5_161, List.forall_mem_cons.2 ⟨subd4_5_162, List.forall_mem_cons.2 ⟨subd4_5_163, List.forall_mem_cons.2 ⟨subd4_5_164, List.forall_mem_cons.2 ⟨subd4_5_165, List.forall_mem_cons.2 ⟨subd4_5_166, List.forall_mem_cons.2 ⟨subd4_5_167, List.forall_mem_cons.2 ⟨subd4_5_168, List.forall_mem_cons.2 ⟨subd4_5_169, List.forall_mem_cons.2 ⟨subd4_5_170, List.forall_mem_cons.2 ⟨subd4_5_171, List.forall_mem_cons.2 ⟨subd4_5_172, List.forall_mem_cons.2 ⟨subd4_5_173, List.forall_mem_cons.2 ⟨subd4_5_174, List.forall_mem_cons.2 ⟨subd4_5_175, List.forall_mem_cons.2 ⟨subd4_5_176, List.forall_mem_cons.2 ⟨subd4_5_177, List.forall_mem_cons.2 ⟨subd4_5_178, List.forall_mem_cons.2 ⟨subd4_5_179, List.forall_mem_cons.2 ⟨subd4_5_180, List.forall_mem_cons.2 ⟨subd4_5_181, List.forall_mem_cons.2 ⟨subd4_5_182, List.forall_mem_cons.2 ⟨subd4_5_183, List.forall_mem_cons.2 ⟨subd4_5_184, List.forall_mem_cons.2 ⟨subd4_5_185, List.forall_mem_cons.2 ⟨subd4_5_186, List.forall_mem_cons.2 ⟨subd4_5_187, List.forall_mem_cons.2 ⟨subd4_5_188, List.forall_mem_cons.2 ⟨subd4_5_189, List.forall_mem_cons.2 ⟨subd4_5_190, List.forall_mem_cons.2 ⟨subd4_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_192 : subd4_5 [0, 0, -7] = true := by decide +kernel
theorem subd4_5_193 : subd4_5 [0, 0, -6] = true := by decide +kernel
theorem subd4_5_194 : subd4_5 [0, 0, -5] = true := by decide +kernel
theorem subd4_5_195 : subd4_5 [0, 0, -4] = true := by decide +kernel
theorem subd4_5_196 : subd4_5 [0, 0, -3] = true := by decide +kernel
theorem subd4_5_197 : subd4_5 [0, 0, -2] = true := by decide +kernel
theorem subd4_5_198 : subd4_5 [0, 0, -1] = true := by decide +kernel
theorem subd4_5_199 : subd4_5 [0, 0, 0] = true := by decide +kernel
theorem subd4_5_200 : subd4_5 [0, 0, 1] = true := by decide +kernel
theorem subd4_5_201 : subd4_5 [0, 0, 2] = true := by decide +kernel
theorem subd4_5_202 : subd4_5 [0, 0, 3] = true := by decide +kernel
theorem subd4_5_203 : subd4_5 [0, 0, 4] = true := by decide +kernel
theorem subd4_5_204 : subd4_5 [0, 0, 5] = true := by decide +kernel
theorem subd4_5_205 : subd4_5 [0, 0, 6] = true := by decide +kernel
theorem subd4_5_206 : subd4_5 [0, 0, 7] = true := by decide +kernel
theorem subd4_5_207 : subd4_5 [0, 0, 8] = true := by decide +kernel
theorem subd4_5_208 : subd4_5 [0, 0, 9] = true := by decide +kernel
theorem subd4_5_209 : subd4_5 [0, 0, 10] = true := by decide +kernel
theorem subd4_5_210 : subd4_5 [0, 0, 11] = true := by decide +kernel
theorem subd4_5_211 : subd4_5 [0, 1, -12] = true := by decide +kernel
theorem subd4_5_212 : subd4_5 [0, 1, -11] = true := by decide +kernel
theorem subd4_5_213 : subd4_5 [0, 1, -10] = true := by decide +kernel
theorem subd4_5_214 : subd4_5 [0, 1, -9] = true := by decide +kernel
theorem subd4_5_215 : subd4_5 [0, 1, -8] = true := by decide +kernel
theorem subd4_5_216 : subd4_5 [0, 1, -7] = true := by decide +kernel
theorem subd4_5_217 : subd4_5 [0, 1, -6] = true := by decide +kernel
theorem subd4_5_218 : subd4_5 [0, 1, -5] = true := by decide +kernel
theorem subd4_5_219 : subd4_5 [0, 1, -4] = true := by decide +kernel
theorem subd4_5_220 : subd4_5 [0, 1, -3] = true := by decide +kernel
theorem subd4_5_221 : subd4_5 [0, 1, -2] = true := by decide +kernel
theorem subd4_5_222 : subd4_5 [0, 1, -1] = true := by decide +kernel
theorem subd4_5_223 : subd4_5 [0, 1, 0] = true := by decide +kernel
theorem sbd4_5_6 : ∀ q ∈ blkd4_5_6, subd4_5 q = true := by
  unfold blkd4_5_6
  exact List.forall_mem_cons.2 ⟨subd4_5_192, List.forall_mem_cons.2 ⟨subd4_5_193, List.forall_mem_cons.2 ⟨subd4_5_194, List.forall_mem_cons.2 ⟨subd4_5_195, List.forall_mem_cons.2 ⟨subd4_5_196, List.forall_mem_cons.2 ⟨subd4_5_197, List.forall_mem_cons.2 ⟨subd4_5_198, List.forall_mem_cons.2 ⟨subd4_5_199, List.forall_mem_cons.2 ⟨subd4_5_200, List.forall_mem_cons.2 ⟨subd4_5_201, List.forall_mem_cons.2 ⟨subd4_5_202, List.forall_mem_cons.2 ⟨subd4_5_203, List.forall_mem_cons.2 ⟨subd4_5_204, List.forall_mem_cons.2 ⟨subd4_5_205, List.forall_mem_cons.2 ⟨subd4_5_206, List.forall_mem_cons.2 ⟨subd4_5_207, List.forall_mem_cons.2 ⟨subd4_5_208, List.forall_mem_cons.2 ⟨subd4_5_209, List.forall_mem_cons.2 ⟨subd4_5_210, List.forall_mem_cons.2 ⟨subd4_5_211, List.forall_mem_cons.2 ⟨subd4_5_212, List.forall_mem_cons.2 ⟨subd4_5_213, List.forall_mem_cons.2 ⟨subd4_5_214, List.forall_mem_cons.2 ⟨subd4_5_215, List.forall_mem_cons.2 ⟨subd4_5_216, List.forall_mem_cons.2 ⟨subd4_5_217, List.forall_mem_cons.2 ⟨subd4_5_218, List.forall_mem_cons.2 ⟨subd4_5_219, List.forall_mem_cons.2 ⟨subd4_5_220, List.forall_mem_cons.2 ⟨subd4_5_221, List.forall_mem_cons.2 ⟨subd4_5_222, List.forall_mem_cons.2 ⟨subd4_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_224 : subd4_5 [0, 1, 1] = true := by decide +kernel
theorem subd4_5_225 : subd4_5 [0, 1, 2] = true := by decide +kernel
theorem subd4_5_226 : subd4_5 [0, 1, 3] = true := by decide +kernel
theorem subd4_5_227 : subd4_5 [0, 1, 4] = true := by decide +kernel
theorem subd4_5_228 : subd4_5 [0, 1, 5] = true := by decide +kernel
theorem subd4_5_229 : subd4_5 [0, 1, 6] = true := by decide +kernel
theorem subd4_5_230 : subd4_5 [0, 1, 7] = true := by decide +kernel
theorem subd4_5_231 : subd4_5 [0, 1, 8] = true := by decide +kernel
theorem subd4_5_232 : subd4_5 [0, 1, 9] = true := by decide +kernel
theorem subd4_5_233 : subd4_5 [0, 1, 10] = true := by decide +kernel
theorem subd4_5_234 : subd4_5 [0, 1, 11] = true := by decide +kernel
theorem subd4_5_235 : subd4_5 [0, 2, -9] = true := by decide +kernel
theorem subd4_5_236 : subd4_5 [0, 2, -8] = true := by decide +kernel
theorem subd4_5_237 : subd4_5 [0, 2, -7] = true := by decide +kernel
theorem subd4_5_238 : subd4_5 [0, 2, -6] = true := by decide +kernel
theorem subd4_5_239 : subd4_5 [0, 2, -5] = true := by decide +kernel
theorem subd4_5_240 : subd4_5 [0, 2, -4] = true := by decide +kernel
theorem subd4_5_241 : subd4_5 [0, 2, -3] = true := by decide +kernel
theorem subd4_5_242 : subd4_5 [0, 2, -2] = true := by decide +kernel
theorem subd4_5_243 : subd4_5 [0, 2, -1] = true := by decide +kernel
theorem subd4_5_244 : subd4_5 [0, 2, 0] = true := by decide +kernel
theorem subd4_5_245 : subd4_5 [0, 2, 1] = true := by decide +kernel
theorem subd4_5_246 : subd4_5 [0, 2, 2] = true := by decide +kernel
theorem subd4_5_247 : subd4_5 [0, 2, 3] = true := by decide +kernel
theorem subd4_5_248 : subd4_5 [0, 2, 4] = true := by decide +kernel
theorem subd4_5_249 : subd4_5 [0, 2, 5] = true := by decide +kernel
theorem subd4_5_250 : subd4_5 [0, 2, 6] = true := by decide +kernel
theorem subd4_5_251 : subd4_5 [0, 2, 7] = true := by decide +kernel
theorem subd4_5_252 : subd4_5 [0, 2, 8] = true := by decide +kernel
theorem subd4_5_253 : subd4_5 [1, -3] = true := by decide +kernel
theorem subd4_5_254 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_255 : subd4_5 [1, -1, -10] = true := by decide +kernel
theorem sbd4_5_7 : ∀ q ∈ blkd4_5_7, subd4_5 q = true := by
  unfold blkd4_5_7
  exact List.forall_mem_cons.2 ⟨subd4_5_224, List.forall_mem_cons.2 ⟨subd4_5_225, List.forall_mem_cons.2 ⟨subd4_5_226, List.forall_mem_cons.2 ⟨subd4_5_227, List.forall_mem_cons.2 ⟨subd4_5_228, List.forall_mem_cons.2 ⟨subd4_5_229, List.forall_mem_cons.2 ⟨subd4_5_230, List.forall_mem_cons.2 ⟨subd4_5_231, List.forall_mem_cons.2 ⟨subd4_5_232, List.forall_mem_cons.2 ⟨subd4_5_233, List.forall_mem_cons.2 ⟨subd4_5_234, List.forall_mem_cons.2 ⟨subd4_5_235, List.forall_mem_cons.2 ⟨subd4_5_236, List.forall_mem_cons.2 ⟨subd4_5_237, List.forall_mem_cons.2 ⟨subd4_5_238, List.forall_mem_cons.2 ⟨subd4_5_239, List.forall_mem_cons.2 ⟨subd4_5_240, List.forall_mem_cons.2 ⟨subd4_5_241, List.forall_mem_cons.2 ⟨subd4_5_242, List.forall_mem_cons.2 ⟨subd4_5_243, List.forall_mem_cons.2 ⟨subd4_5_244, List.forall_mem_cons.2 ⟨subd4_5_245, List.forall_mem_cons.2 ⟨subd4_5_246, List.forall_mem_cons.2 ⟨subd4_5_247, List.forall_mem_cons.2 ⟨subd4_5_248, List.forall_mem_cons.2 ⟨subd4_5_249, List.forall_mem_cons.2 ⟨subd4_5_250, List.forall_mem_cons.2 ⟨subd4_5_251, List.forall_mem_cons.2 ⟨subd4_5_252, List.forall_mem_cons.2 ⟨subd4_5_253, List.forall_mem_cons.2 ⟨subd4_5_254, List.forall_mem_cons.2 ⟨subd4_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_256 : subd4_5 [1, -1, -9] = true := by decide +kernel
theorem subd4_5_257 : subd4_5 [1, -1, -8] = true := by decide +kernel
theorem subd4_5_258 : subd4_5 [1, -1, -7] = true := by decide +kernel
theorem subd4_5_259 : subd4_5 [1, -1, -6] = true := by decide +kernel
theorem subd4_5_260 : subd4_5 [1, -1, -5] = true := by decide +kernel
theorem subd4_5_261 : subd4_5 [1, -1, -4] = true := by decide +kernel
theorem subd4_5_262 : subd4_5 [1, -1, -3] = true := by decide +kernel
theorem subd4_5_263 : subd4_5 [1, -1, -2] = true := by decide +kernel
theorem subd4_5_264 : subd4_5 [1, -1, -1] = true := by decide +kernel
theorem subd4_5_265 : subd4_5 [1, -1, 0] = true := by decide +kernel
theorem subd4_5_266 : subd4_5 [1, -1, 1] = true := by decide +kernel
theorem subd4_5_267 : subd4_5 [1, -1, 2] = true := by decide +kernel
theorem subd4_5_268 : subd4_5 [1, -1, 3] = true := by decide +kernel
theorem subd4_5_269 : subd4_5 [1, -1, 4] = true := by decide +kernel
theorem subd4_5_270 : subd4_5 [1, -1, 5] = true := by decide +kernel
theorem subd4_5_271 : subd4_5 [1, -1, 6] = true := by decide +kernel
theorem subd4_5_272 : subd4_5 [1, -1, 7] = true := by decide +kernel
theorem subd4_5_273 : subd4_5 [1, -1, 8] = true := by decide +kernel
theorem subd4_5_274 : subd4_5 [1, -1, 9] = true := by decide +kernel
theorem subd4_5_275 : subd4_5 [1, -1, 10] = true := by decide +kernel
theorem subd4_5_276 : subd4_5 [1, 0, -11] = true := by decide +kernel
theorem subd4_5_277 : subd4_5 [1, 0, -10] = true := by decide +kernel
theorem subd4_5_278 : subd4_5 [1, 0, -9] = true := by decide +kernel
theorem subd4_5_279 : subd4_5 [1, 0, -8] = true := by decide +kernel
theorem subd4_5_280 : subd4_5 [1, 0, -7] = true := by decide +kernel
theorem subd4_5_281 : subd4_5 [1, 0, -6] = true := by decide +kernel
theorem subd4_5_282 : subd4_5 [1, 0, -5] = true := by decide +kernel
theorem subd4_5_283 : subd4_5 [1, 0, -4] = true := by decide +kernel
theorem subd4_5_284 : subd4_5 [1, 0, -3] = true := by decide +kernel
theorem subd4_5_285 : subd4_5 [1, 0, -2] = true := by decide +kernel
theorem subd4_5_286 : subd4_5 [1, 0, -1] = true := by decide +kernel
theorem subd4_5_287 : subd4_5 [1, 0, 0] = true := by decide +kernel
theorem sbd4_5_8 : ∀ q ∈ blkd4_5_8, subd4_5 q = true := by
  unfold blkd4_5_8
  exact List.forall_mem_cons.2 ⟨subd4_5_256, List.forall_mem_cons.2 ⟨subd4_5_257, List.forall_mem_cons.2 ⟨subd4_5_258, List.forall_mem_cons.2 ⟨subd4_5_259, List.forall_mem_cons.2 ⟨subd4_5_260, List.forall_mem_cons.2 ⟨subd4_5_261, List.forall_mem_cons.2 ⟨subd4_5_262, List.forall_mem_cons.2 ⟨subd4_5_263, List.forall_mem_cons.2 ⟨subd4_5_264, List.forall_mem_cons.2 ⟨subd4_5_265, List.forall_mem_cons.2 ⟨subd4_5_266, List.forall_mem_cons.2 ⟨subd4_5_267, List.forall_mem_cons.2 ⟨subd4_5_268, List.forall_mem_cons.2 ⟨subd4_5_269, List.forall_mem_cons.2 ⟨subd4_5_270, List.forall_mem_cons.2 ⟨subd4_5_271, List.forall_mem_cons.2 ⟨subd4_5_272, List.forall_mem_cons.2 ⟨subd4_5_273, List.forall_mem_cons.2 ⟨subd4_5_274, List.forall_mem_cons.2 ⟨subd4_5_275, List.forall_mem_cons.2 ⟨subd4_5_276, List.forall_mem_cons.2 ⟨subd4_5_277, List.forall_mem_cons.2 ⟨subd4_5_278, List.forall_mem_cons.2 ⟨subd4_5_279, List.forall_mem_cons.2 ⟨subd4_5_280, List.forall_mem_cons.2 ⟨subd4_5_281, List.forall_mem_cons.2 ⟨subd4_5_282, List.forall_mem_cons.2 ⟨subd4_5_283, List.forall_mem_cons.2 ⟨subd4_5_284, List.forall_mem_cons.2 ⟨subd4_5_285, List.forall_mem_cons.2 ⟨subd4_5_286, List.forall_mem_cons.2 ⟨subd4_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
