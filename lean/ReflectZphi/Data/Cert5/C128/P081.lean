import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_5_0 : subd11_5 [-4] = true := by decide +kernel
theorem subd11_5_1 : subd11_5 [-3] = true := by decide +kernel
theorem subd11_5_2 : subd11_5 [-2, -4] = true := by decide +kernel
theorem subd11_5_3 : subd11_5 [-2, -3] = true := by decide +kernel
theorem subd11_5_4 : subd11_5 [-2, -2] = true := by decide +kernel
theorem subd11_5_5 : subd11_5 [-2, -1] = true := by decide +kernel
theorem subd11_5_6 : subd11_5 [-2, 0] = true := by decide +kernel
theorem subd11_5_7 : subd11_5 [-2, 1] = true := by decide +kernel
theorem subd11_5_8 : subd11_5 [-2, 2] = true := by decide +kernel
theorem subd11_5_9 : subd11_5 [-2, 3] = true := by decide +kernel
theorem subd11_5_10 : subd11_5 [-1, -4] = true := by decide +kernel
theorem subd11_5_11 : subd11_5 [-1, -3] = true := by decide +kernel
theorem subd11_5_12 : subd11_5 [-1, -2] = true := by decide +kernel
theorem subd11_5_13 : subd11_5 [-1, -1] = true := by decide +kernel
theorem subd11_5_14 : subd11_5 [-1, 0] = true := by decide +kernel
theorem subd11_5_15 : subd11_5 [-1, 1] = true := by decide +kernel
theorem subd11_5_16 : subd11_5 [-1, 2] = true := by decide +kernel
theorem subd11_5_17 : subd11_5 [-1, 3] = true := by decide +kernel
theorem subd11_5_18 : subd11_5 [0, -4] = true := by decide +kernel
theorem subd11_5_19 : subd11_5 [0, -3] = true := by decide +kernel
theorem subd11_5_20 : subd11_5 [0, -2] = true := by decide +kernel
theorem subd11_5_21 : subd11_5 [0, -1] = true := by decide +kernel
theorem subd11_5_22 : subd11_5 [0, 0] = true := by decide +kernel
theorem subd11_5_23 : subd11_5 [0, 1] = true := by decide +kernel
theorem subd11_5_24 : subd11_5 [0, 2] = true := by decide +kernel
theorem subd11_5_25 : subd11_5 [0, 3] = true := by decide +kernel
theorem subd11_5_26 : subd11_5 [1, -4] = true := by decide +kernel
theorem subd11_5_27 : subd11_5 [1, -3] = true := by decide +kernel
theorem subd11_5_28 : subd11_5 [1, -2] = true := by decide +kernel
theorem subd11_5_29 : subd11_5 [1, -1] = true := by decide +kernel
theorem subd11_5_30 : subd11_5 [1, 0] = true := by decide +kernel
theorem subd11_5_31 : subd11_5 [1, 1] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_cons.2 ⟨subd11_5_1, List.forall_mem_cons.2 ⟨subd11_5_2, List.forall_mem_cons.2 ⟨subd11_5_3, List.forall_mem_cons.2 ⟨subd11_5_4, List.forall_mem_cons.2 ⟨subd11_5_5, List.forall_mem_cons.2 ⟨subd11_5_6, List.forall_mem_cons.2 ⟨subd11_5_7, List.forall_mem_cons.2 ⟨subd11_5_8, List.forall_mem_cons.2 ⟨subd11_5_9, List.forall_mem_cons.2 ⟨subd11_5_10, List.forall_mem_cons.2 ⟨subd11_5_11, List.forall_mem_cons.2 ⟨subd11_5_12, List.forall_mem_cons.2 ⟨subd11_5_13, List.forall_mem_cons.2 ⟨subd11_5_14, List.forall_mem_cons.2 ⟨subd11_5_15, List.forall_mem_cons.2 ⟨subd11_5_16, List.forall_mem_cons.2 ⟨subd11_5_17, List.forall_mem_cons.2 ⟨subd11_5_18, List.forall_mem_cons.2 ⟨subd11_5_19, List.forall_mem_cons.2 ⟨subd11_5_20, List.forall_mem_cons.2 ⟨subd11_5_21, List.forall_mem_cons.2 ⟨subd11_5_22, List.forall_mem_cons.2 ⟨subd11_5_23, List.forall_mem_cons.2 ⟨subd11_5_24, List.forall_mem_cons.2 ⟨subd11_5_25, List.forall_mem_cons.2 ⟨subd11_5_26, List.forall_mem_cons.2 ⟨subd11_5_27, List.forall_mem_cons.2 ⟨subd11_5_28, List.forall_mem_cons.2 ⟨subd11_5_29, List.forall_mem_cons.2 ⟨subd11_5_30, List.forall_mem_cons.2 ⟨subd11_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_32 : subd11_5 [1, 2] = true := by decide +kernel
theorem subd11_5_33 : subd11_5 [1, 3] = true := by decide +kernel
theorem subd11_5_34 : subd11_5 [2, -4] = true := by decide +kernel
theorem subd11_5_35 : subd11_5 [2, -3] = true := by decide +kernel
theorem subd11_5_36 : subd11_5 [2, -2] = true := by decide +kernel
theorem subd11_5_37 : subd11_5 [2, -1] = true := by decide +kernel
theorem subd11_5_38 : subd11_5 [2, 0] = true := by decide +kernel
theorem subd11_5_39 : subd11_5 [2, 1] = true := by decide +kernel
theorem subd11_5_40 : subd11_5 [2, 2] = true := by decide +kernel
theorem subd11_5_41 : subd11_5 [2, 3] = true := by decide +kernel
theorem subd11_5_42 : subd11_5 [3] = true := by decide +kernel
theorem subd11_5_43 : subd11_5 [4] = true := by decide +kernel
theorem sbd11_5_1 : ∀ q ∈ blkd11_5_1, subd11_5 q = true := by
  unfold blkd11_5_1
  exact List.forall_mem_cons.2 ⟨subd11_5_32, List.forall_mem_cons.2 ⟨subd11_5_33, List.forall_mem_cons.2 ⟨subd11_5_34, List.forall_mem_cons.2 ⟨subd11_5_35, List.forall_mem_cons.2 ⟨subd11_5_36, List.forall_mem_cons.2 ⟨subd11_5_37, List.forall_mem_cons.2 ⟨subd11_5_38, List.forall_mem_cons.2 ⟨subd11_5_39, List.forall_mem_cons.2 ⟨subd11_5_40, List.forall_mem_cons.2 ⟨subd11_5_41, List.forall_mem_cons.2 ⟨subd11_5_42, List.forall_mem_cons.2 ⟨subd11_5_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_6 : ldCheck G d11_6.U d11_6.ms ldd11_6 = true := by decide +kernel
theorem pre_okd11_6 : subPre G cell11 d11_6 = true := by decide +kernel
theorem subd11_6_0 : subd11_6 [-1, -2] = true := by decide +kernel
theorem subd11_6_1 : subd11_6 [-1, -1, -7] = true := by decide +kernel
theorem subd11_6_2 : subd11_6 [-1, -1, -6] = true := by decide +kernel
theorem subd11_6_3 : subd11_6 [-1, -1, -5] = true := by decide +kernel
theorem subd11_6_4 : subd11_6 [-1, -1, -4] = true := by decide +kernel
theorem subd11_6_5 : subd11_6 [-1, -1, -3] = true := by decide +kernel
theorem subd11_6_6 : subd11_6 [-1, -1, -2] = true := by decide +kernel
theorem subd11_6_7 : subd11_6 [-1, -1, -1] = true := by decide +kernel
theorem subd11_6_8 : subd11_6 [-1, -1, 0] = true := by decide +kernel
theorem subd11_6_9 : subd11_6 [-1, -1, 1] = true := by decide +kernel
theorem subd11_6_10 : subd11_6 [-1, -1, 2] = true := by decide +kernel
theorem subd11_6_11 : subd11_6 [-1, -1, 3] = true := by decide +kernel
theorem subd11_6_12 : subd11_6 [-1, -1, 4] = true := by decide +kernel
theorem subd11_6_13 : subd11_6 [-1, -1, 5] = true := by decide +kernel
theorem subd11_6_14 : subd11_6 [-1, -1, 6] = true := by decide +kernel
theorem subd11_6_15 : subd11_6 [-1, -1, 7] = true := by decide +kernel
theorem subd11_6_16 : subd11_6 [-1, 0, -8] = true := by decide +kernel
theorem subd11_6_17 : subd11_6 [-1, 0, -7] = true := by decide +kernel
theorem subd11_6_18 : subd11_6 [-1, 0, -6] = true := by decide +kernel
theorem subd11_6_19 : subd11_6 [-1, 0, -5] = true := by decide +kernel
theorem subd11_6_20 : subd11_6 [-1, 0, -4] = true := by decide +kernel
theorem subd11_6_21 : subd11_6 [-1, 0, -3] = true := by decide +kernel
theorem subd11_6_22 : subd11_6 [-1, 0, -2] = true := by decide +kernel
theorem subd11_6_23 : subd11_6 [-1, 0, -1] = true := by decide +kernel
theorem subd11_6_24 : subd11_6 [-1, 0, 0] = true := by decide +kernel
theorem subd11_6_25 : subd11_6 [-1, 0, 1] = true := by decide +kernel
theorem subd11_6_26 : subd11_6 [-1, 0, 2] = true := by decide +kernel
theorem subd11_6_27 : subd11_6 [-1, 0, 3] = true := by decide +kernel
theorem subd11_6_28 : subd11_6 [-1, 0, 4] = true := by decide +kernel
theorem subd11_6_29 : subd11_6 [-1, 0, 5] = true := by decide +kernel
theorem subd11_6_30 : subd11_6 [-1, 0, 6] = true := by decide +kernel
theorem subd11_6_31 : subd11_6 [-1, 0, 7] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_cons.2 ⟨subd11_6_1, List.forall_mem_cons.2 ⟨subd11_6_2, List.forall_mem_cons.2 ⟨subd11_6_3, List.forall_mem_cons.2 ⟨subd11_6_4, List.forall_mem_cons.2 ⟨subd11_6_5, List.forall_mem_cons.2 ⟨subd11_6_6, List.forall_mem_cons.2 ⟨subd11_6_7, List.forall_mem_cons.2 ⟨subd11_6_8, List.forall_mem_cons.2 ⟨subd11_6_9, List.forall_mem_cons.2 ⟨subd11_6_10, List.forall_mem_cons.2 ⟨subd11_6_11, List.forall_mem_cons.2 ⟨subd11_6_12, List.forall_mem_cons.2 ⟨subd11_6_13, List.forall_mem_cons.2 ⟨subd11_6_14, List.forall_mem_cons.2 ⟨subd11_6_15, List.forall_mem_cons.2 ⟨subd11_6_16, List.forall_mem_cons.2 ⟨subd11_6_17, List.forall_mem_cons.2 ⟨subd11_6_18, List.forall_mem_cons.2 ⟨subd11_6_19, List.forall_mem_cons.2 ⟨subd11_6_20, List.forall_mem_cons.2 ⟨subd11_6_21, List.forall_mem_cons.2 ⟨subd11_6_22, List.forall_mem_cons.2 ⟨subd11_6_23, List.forall_mem_cons.2 ⟨subd11_6_24, List.forall_mem_cons.2 ⟨subd11_6_25, List.forall_mem_cons.2 ⟨subd11_6_26, List.forall_mem_cons.2 ⟨subd11_6_27, List.forall_mem_cons.2 ⟨subd11_6_28, List.forall_mem_cons.2 ⟨subd11_6_29, List.forall_mem_cons.2 ⟨subd11_6_30, List.forall_mem_cons.2 ⟨subd11_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_6_32 : subd11_6 [-1, 1] = true := by decide +kernel
theorem subd11_6_33 : subd11_6 [0, -3] = true := by decide +kernel
theorem subd11_6_34 : subd11_6 [0, -2] = true := by decide +kernel
theorem subd11_6_35 : subd11_6 [0, -1, -8] = true := by decide +kernel
theorem subd11_6_36 : subd11_6 [0, -1, -7] = true := by decide +kernel
theorem subd11_6_37 : subd11_6 [0, -1, -6] = true := by decide +kernel
theorem subd11_6_38 : subd11_6 [0, -1, -5] = true := by decide +kernel
theorem subd11_6_39 : subd11_6 [0, -1, -4] = true := by decide +kernel
theorem subd11_6_40 : subd11_6 [0, -1, -3] = true := by decide +kernel
theorem subd11_6_41 : subd11_6 [0, -1, -2] = true := by decide +kernel
theorem subd11_6_42 : subd11_6 [0, -1, -1] = true := by decide +kernel
theorem subd11_6_43 : subd11_6 [0, -1, 0] = true := by decide +kernel
theorem subd11_6_44 : subd11_6 [0, -1, 1] = true := by decide +kernel
theorem subd11_6_45 : subd11_6 [0, -1, 2] = true := by decide +kernel
theorem subd11_6_46 : subd11_6 [0, -1, 3] = true := by decide +kernel
theorem subd11_6_47 : subd11_6 [0, -1, 4] = true := by decide +kernel
theorem subd11_6_48 : subd11_6 [0, -1, 5] = true := by decide +kernel
theorem subd11_6_49 : subd11_6 [0, -1, 6] = true := by decide +kernel
theorem subd11_6_50 : subd11_6 [0, -1, 7] = true := by decide +kernel
theorem subd11_6_51 : subd11_6 [0, -1, 8] = true := by decide +kernel
theorem subd11_6_52 : subd11_6 [0, 0, -10] = true := by decide +kernel
theorem subd11_6_53 : subd11_6 [0, 0, -9] = true := by decide +kernel
theorem subd11_6_54 : subd11_6 [0, 0, -8] = true := by decide +kernel
theorem subd11_6_55 : subd11_6 [0, 0, -7] = true := by decide +kernel
theorem subd11_6_56 : subd11_6 [0, 0, -6] = true := by decide +kernel
theorem subd11_6_57 : subd11_6 [0, 0, -5] = true := by decide +kernel
theorem subd11_6_58 : subd11_6 [0, 0, -4] = true := by decide +kernel
theorem subd11_6_59 : subd11_6 [0, 0, -3] = true := by decide +kernel
theorem subd11_6_60 : subd11_6 [0, 0, -2] = true := by decide +kernel
theorem subd11_6_61 : subd11_6 [0, 0, -1] = true := by decide +kernel
theorem subd11_6_62 : subd11_6 [0, 0, 0] = true := by decide +kernel
theorem subd11_6_63 : subd11_6 [0, 0, 1] = true := by decide +kernel
theorem sbd11_6_1 : ∀ q ∈ blkd11_6_1, subd11_6 q = true := by
  unfold blkd11_6_1
  exact List.forall_mem_cons.2 ⟨subd11_6_32, List.forall_mem_cons.2 ⟨subd11_6_33, List.forall_mem_cons.2 ⟨subd11_6_34, List.forall_mem_cons.2 ⟨subd11_6_35, List.forall_mem_cons.2 ⟨subd11_6_36, List.forall_mem_cons.2 ⟨subd11_6_37, List.forall_mem_cons.2 ⟨subd11_6_38, List.forall_mem_cons.2 ⟨subd11_6_39, List.forall_mem_cons.2 ⟨subd11_6_40, List.forall_mem_cons.2 ⟨subd11_6_41, List.forall_mem_cons.2 ⟨subd11_6_42, List.forall_mem_cons.2 ⟨subd11_6_43, List.forall_mem_cons.2 ⟨subd11_6_44, List.forall_mem_cons.2 ⟨subd11_6_45, List.forall_mem_cons.2 ⟨subd11_6_46, List.forall_mem_cons.2 ⟨subd11_6_47, List.forall_mem_cons.2 ⟨subd11_6_48, List.forall_mem_cons.2 ⟨subd11_6_49, List.forall_mem_cons.2 ⟨subd11_6_50, List.forall_mem_cons.2 ⟨subd11_6_51, List.forall_mem_cons.2 ⟨subd11_6_52, List.forall_mem_cons.2 ⟨subd11_6_53, List.forall_mem_cons.2 ⟨subd11_6_54, List.forall_mem_cons.2 ⟨subd11_6_55, List.forall_mem_cons.2 ⟨subd11_6_56, List.forall_mem_cons.2 ⟨subd11_6_57, List.forall_mem_cons.2 ⟨subd11_6_58, List.forall_mem_cons.2 ⟨subd11_6_59, List.forall_mem_cons.2 ⟨subd11_6_60, List.forall_mem_cons.2 ⟨subd11_6_61, List.forall_mem_cons.2 ⟨subd11_6_62, List.forall_mem_cons.2 ⟨subd11_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_6_64 : subd11_6 [0, 0, 2] = true := by decide +kernel
theorem subd11_6_65 : subd11_6 [0, 0, 3] = true := by decide +kernel
theorem subd11_6_66 : subd11_6 [0, 0, 4] = true := by decide +kernel
theorem subd11_6_67 : subd11_6 [0, 0, 5] = true := by decide +kernel
theorem subd11_6_68 : subd11_6 [0, 0, 6] = true := by decide +kernel
theorem subd11_6_69 : subd11_6 [0, 0, 7] = true := by decide +kernel
theorem subd11_6_70 : subd11_6 [0, 0, 8] = true := by decide +kernel
theorem subd11_6_71 : subd11_6 [0, 0, 9] = true := by decide +kernel
theorem subd11_6_72 : subd11_6 [0, 1, -9] = true := by decide +kernel
theorem subd11_6_73 : subd11_6 [0, 1, -8] = true := by decide +kernel
theorem subd11_6_74 : subd11_6 [0, 1, -7] = true := by decide +kernel
theorem subd11_6_75 : subd11_6 [0, 1, -6] = true := by decide +kernel
theorem subd11_6_76 : subd11_6 [0, 1, -5] = true := by decide +kernel
theorem subd11_6_77 : subd11_6 [0, 1, -4] = true := by decide +kernel
theorem subd11_6_78 : subd11_6 [0, 1, -3] = true := by decide +kernel
theorem subd11_6_79 : subd11_6 [0, 1, -2] = true := by decide +kernel
theorem subd11_6_80 : subd11_6 [0, 1, -1] = true := by decide +kernel
theorem subd11_6_81 : subd11_6 [0, 1, 0] = true := by decide +kernel
theorem subd11_6_82 : subd11_6 [0, 1, 1] = true := by decide +kernel
theorem subd11_6_83 : subd11_6 [0, 1, 2] = true := by decide +kernel
theorem subd11_6_84 : subd11_6 [0, 1, 3] = true := by decide +kernel
theorem subd11_6_85 : subd11_6 [0, 1, 4] = true := by decide +kernel
theorem subd11_6_86 : subd11_6 [0, 1, 5] = true := by decide +kernel
theorem subd11_6_87 : subd11_6 [0, 1, 6] = true := by decide +kernel
theorem subd11_6_88 : subd11_6 [0, 1, 7] = true := by decide +kernel
theorem subd11_6_89 : subd11_6 [0, 2] = true := by decide +kernel
theorem subd11_6_90 : subd11_6 [1, -2] = true := by decide +kernel
theorem subd11_6_91 : subd11_6 [1, -1] = true := by decide +kernel
theorem subd11_6_92 : subd11_6 [1, 0, -8] = true := by decide +kernel
theorem subd11_6_93 : subd11_6 [1, 0, -7] = true := by decide +kernel
theorem subd11_6_94 : subd11_6 [1, 0, -6] = true := by decide +kernel
theorem subd11_6_95 : subd11_6 [1, 0, -5] = true := by decide +kernel
theorem sbd11_6_2 : ∀ q ∈ blkd11_6_2, subd11_6 q = true := by
  unfold blkd11_6_2
  exact List.forall_mem_cons.2 ⟨subd11_6_64, List.forall_mem_cons.2 ⟨subd11_6_65, List.forall_mem_cons.2 ⟨subd11_6_66, List.forall_mem_cons.2 ⟨subd11_6_67, List.forall_mem_cons.2 ⟨subd11_6_68, List.forall_mem_cons.2 ⟨subd11_6_69, List.forall_mem_cons.2 ⟨subd11_6_70, List.forall_mem_cons.2 ⟨subd11_6_71, List.forall_mem_cons.2 ⟨subd11_6_72, List.forall_mem_cons.2 ⟨subd11_6_73, List.forall_mem_cons.2 ⟨subd11_6_74, List.forall_mem_cons.2 ⟨subd11_6_75, List.forall_mem_cons.2 ⟨subd11_6_76, List.forall_mem_cons.2 ⟨subd11_6_77, List.forall_mem_cons.2 ⟨subd11_6_78, List.forall_mem_cons.2 ⟨subd11_6_79, List.forall_mem_cons.2 ⟨subd11_6_80, List.forall_mem_cons.2 ⟨subd11_6_81, List.forall_mem_cons.2 ⟨subd11_6_82, List.forall_mem_cons.2 ⟨subd11_6_83, List.forall_mem_cons.2 ⟨subd11_6_84, List.forall_mem_cons.2 ⟨subd11_6_85, List.forall_mem_cons.2 ⟨subd11_6_86, List.forall_mem_cons.2 ⟨subd11_6_87, List.forall_mem_cons.2 ⟨subd11_6_88, List.forall_mem_cons.2 ⟨subd11_6_89, List.forall_mem_cons.2 ⟨subd11_6_90, List.forall_mem_cons.2 ⟨subd11_6_91, List.forall_mem_cons.2 ⟨subd11_6_92, List.forall_mem_cons.2 ⟨subd11_6_93, List.forall_mem_cons.2 ⟨subd11_6_94, List.forall_mem_cons.2 ⟨subd11_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_6_96 : subd11_6 [1, 0, -4] = true := by decide +kernel
theorem subd11_6_97 : subd11_6 [1, 0, -3] = true := by decide +kernel
theorem subd11_6_98 : subd11_6 [1, 0, -2] = true := by decide +kernel
theorem subd11_6_99 : subd11_6 [1, 0, -1] = true := by decide +kernel
theorem subd11_6_100 : subd11_6 [1, 0, 0] = true := by decide +kernel
theorem subd11_6_101 : subd11_6 [1, 0, 1] = true := by decide +kernel
theorem subd11_6_102 : subd11_6 [1, 0, 2] = true := by decide +kernel
theorem subd11_6_103 : subd11_6 [1, 0, 3] = true := by decide +kernel
theorem subd11_6_104 : subd11_6 [1, 0, 4] = true := by decide +kernel
theorem subd11_6_105 : subd11_6 [1, 0, 5] = true := by decide +kernel
theorem subd11_6_106 : subd11_6 [1, 0, 6] = true := by decide +kernel
theorem subd11_6_107 : subd11_6 [1, 0, 7] = true := by decide +kernel
theorem subd11_6_108 : subd11_6 [1, 1, -8] = true := by decide +kernel
theorem subd11_6_109 : subd11_6 [1, 1, -7] = true := by decide +kernel
theorem subd11_6_110 : subd11_6 [1, 1, -6] = true := by decide +kernel
theorem subd11_6_111 : subd11_6 [1, 1, -5] = true := by decide +kernel
theorem subd11_6_112 : subd11_6 [1, 1, -4] = true := by decide +kernel
theorem subd11_6_113 : subd11_6 [1, 1, -3] = true := by decide +kernel
theorem subd11_6_114 : subd11_6 [1, 1, -2] = true := by decide +kernel
theorem subd11_6_115 : subd11_6 [1, 1, -1] = true := by decide +kernel
theorem subd11_6_116 : subd11_6 [1, 1, 0] = true := by decide +kernel
theorem subd11_6_117 : subd11_6 [1, 1, 1] = true := by decide +kernel
theorem subd11_6_118 : subd11_6 [1, 1, 2] = true := by decide +kernel
theorem subd11_6_119 : subd11_6 [1, 1, 3] = true := by decide +kernel
theorem subd11_6_120 : subd11_6 [1, 1, 4] = true := by decide +kernel
theorem subd11_6_121 : subd11_6 [1, 1, 5] = true := by decide +kernel
theorem subd11_6_122 : subd11_6 [1, 1, 6] = true := by decide +kernel
theorem sbd11_6_3 : ∀ q ∈ blkd11_6_3, subd11_6 q = true := by
  unfold blkd11_6_3
  exact List.forall_mem_cons.2 ⟨subd11_6_96, List.forall_mem_cons.2 ⟨subd11_6_97, List.forall_mem_cons.2 ⟨subd11_6_98, List.forall_mem_cons.2 ⟨subd11_6_99, List.forall_mem_cons.2 ⟨subd11_6_100, List.forall_mem_cons.2 ⟨subd11_6_101, List.forall_mem_cons.2 ⟨subd11_6_102, List.forall_mem_cons.2 ⟨subd11_6_103, List.forall_mem_cons.2 ⟨subd11_6_104, List.forall_mem_cons.2 ⟨subd11_6_105, List.forall_mem_cons.2 ⟨subd11_6_106, List.forall_mem_cons.2 ⟨subd11_6_107, List.forall_mem_cons.2 ⟨subd11_6_108, List.forall_mem_cons.2 ⟨subd11_6_109, List.forall_mem_cons.2 ⟨subd11_6_110, List.forall_mem_cons.2 ⟨subd11_6_111, List.forall_mem_cons.2 ⟨subd11_6_112, List.forall_mem_cons.2 ⟨subd11_6_113, List.forall_mem_cons.2 ⟨subd11_6_114, List.forall_mem_cons.2 ⟨subd11_6_115, List.forall_mem_cons.2 ⟨subd11_6_116, List.forall_mem_cons.2 ⟨subd11_6_117, List.forall_mem_cons.2 ⟨subd11_6_118, List.forall_mem_cons.2 ⟨subd11_6_119, List.forall_mem_cons.2 ⟨subd11_6_120, List.forall_mem_cons.2 ⟨subd11_6_121, List.forall_mem_cons.2 ⟨subd11_6_122, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_7 : ldCheck G d11_7.U d11_7.ms ldd11_7 = true := by decide +kernel
theorem pre_okd11_7 : subPre G cell11 d11_7 = true := by decide +kernel
theorem subd11_7_0 : subd11_7 [-3] = true := by decide +kernel
theorem subd11_7_1 : subd11_7 [-2, -3] = true := by decide +kernel
theorem subd11_7_2 : subd11_7 [-2, -2] = true := by decide +kernel
theorem subd11_7_3 : subd11_7 [-2, -1] = true := by decide +kernel
theorem subd11_7_4 : subd11_7 [-2, 0] = true := by decide +kernel
theorem subd11_7_5 : subd11_7 [-2, 1] = true := by decide +kernel
theorem subd11_7_6 : subd11_7 [-2, 2] = true := by decide +kernel
theorem subd11_7_7 : subd11_7 [-2, 3] = true := by decide +kernel
theorem subd11_7_8 : subd11_7 [-1, -4] = true := by decide +kernel
theorem subd11_7_9 : subd11_7 [-1, -3] = true := by decide +kernel
theorem subd11_7_10 : subd11_7 [-1, -2] = true := by decide +kernel
theorem subd11_7_11 : subd11_7 [-1, -1] = true := by decide +kernel
theorem subd11_7_12 : subd11_7 [-1, 0] = true := by decide +kernel
theorem subd11_7_13 : subd11_7 [-1, 1] = true := by decide +kernel
theorem subd11_7_14 : subd11_7 [-1, 2] = true := by decide +kernel
theorem subd11_7_15 : subd11_7 [-1, 3] = true := by decide +kernel
theorem subd11_7_16 : subd11_7 [0, -4] = true := by decide +kernel
theorem subd11_7_17 : subd11_7 [0, -3] = true := by decide +kernel
theorem subd11_7_18 : subd11_7 [0, -2] = true := by decide +kernel
theorem subd11_7_19 : subd11_7 [0, -1] = true := by decide +kernel
theorem subd11_7_20 : subd11_7 [0, 0] = true := by decide +kernel
theorem subd11_7_21 : subd11_7 [0, 1] = true := by decide +kernel
theorem subd11_7_22 : subd11_7 [0, 2] = true := by decide +kernel
theorem subd11_7_23 : subd11_7 [0, 3] = true := by decide +kernel
theorem subd11_7_24 : subd11_7 [1, -4] = true := by decide +kernel
theorem subd11_7_25 : subd11_7 [1, -3] = true := by decide +kernel
theorem subd11_7_26 : subd11_7 [1, -2] = true := by decide +kernel
theorem subd11_7_27 : subd11_7 [1, -1] = true := by decide +kernel
theorem subd11_7_28 : subd11_7 [1, 0] = true := by decide +kernel
theorem subd11_7_29 : subd11_7 [1, 1] = true := by decide +kernel
theorem subd11_7_30 : subd11_7 [1, 2] = true := by decide +kernel
theorem subd11_7_31 : subd11_7 [1, 3] = true := by decide +kernel
theorem sbd11_7_0 : ∀ q ∈ blkd11_7_0, subd11_7 q = true := by
  unfold blkd11_7_0
  exact List.forall_mem_cons.2 ⟨subd11_7_0, List.forall_mem_cons.2 ⟨subd11_7_1, List.forall_mem_cons.2 ⟨subd11_7_2, List.forall_mem_cons.2 ⟨subd11_7_3, List.forall_mem_cons.2 ⟨subd11_7_4, List.forall_mem_cons.2 ⟨subd11_7_5, List.forall_mem_cons.2 ⟨subd11_7_6, List.forall_mem_cons.2 ⟨subd11_7_7, List.forall_mem_cons.2 ⟨subd11_7_8, List.forall_mem_cons.2 ⟨subd11_7_9, List.forall_mem_cons.2 ⟨subd11_7_10, List.forall_mem_cons.2 ⟨subd11_7_11, List.forall_mem_cons.2 ⟨subd11_7_12, List.forall_mem_cons.2 ⟨subd11_7_13, List.forall_mem_cons.2 ⟨subd11_7_14, List.forall_mem_cons.2 ⟨subd11_7_15, List.forall_mem_cons.2 ⟨subd11_7_16, List.forall_mem_cons.2 ⟨subd11_7_17, List.forall_mem_cons.2 ⟨subd11_7_18, List.forall_mem_cons.2 ⟨subd11_7_19, List.forall_mem_cons.2 ⟨subd11_7_20, List.forall_mem_cons.2 ⟨subd11_7_21, List.forall_mem_cons.2 ⟨subd11_7_22, List.forall_mem_cons.2 ⟨subd11_7_23, List.forall_mem_cons.2 ⟨subd11_7_24, List.forall_mem_cons.2 ⟨subd11_7_25, List.forall_mem_cons.2 ⟨subd11_7_26, List.forall_mem_cons.2 ⟨subd11_7_27, List.forall_mem_cons.2 ⟨subd11_7_28, List.forall_mem_cons.2 ⟨subd11_7_29, List.forall_mem_cons.2 ⟨subd11_7_30, List.forall_mem_cons.2 ⟨subd11_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_7_32 : subd11_7 [2, -4] = true := by decide +kernel
theorem subd11_7_33 : subd11_7 [2, -3] = true := by decide +kernel
theorem subd11_7_34 : subd11_7 [2, -2] = true := by decide +kernel
theorem subd11_7_35 : subd11_7 [2, -1] = true := by decide +kernel
theorem subd11_7_36 : subd11_7 [2, 0] = true := by decide +kernel
theorem subd11_7_37 : subd11_7 [2, 1] = true := by decide +kernel
theorem subd11_7_38 : subd11_7 [2, 2] = true := by decide +kernel
theorem subd11_7_39 : subd11_7 [3] = true := by decide +kernel
theorem sbd11_7_1 : ∀ q ∈ blkd11_7_1, subd11_7 q = true := by
  unfold blkd11_7_1
  exact List.forall_mem_cons.2 ⟨subd11_7_32, List.forall_mem_cons.2 ⟨subd11_7_33, List.forall_mem_cons.2 ⟨subd11_7_34, List.forall_mem_cons.2 ⟨subd11_7_35, List.forall_mem_cons.2 ⟨subd11_7_36, List.forall_mem_cons.2 ⟨subd11_7_37, List.forall_mem_cons.2 ⟨subd11_7_38, List.forall_mem_cons.2 ⟨subd11_7_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C128
