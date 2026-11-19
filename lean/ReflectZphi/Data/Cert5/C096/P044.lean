import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_4_32 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_33 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_34 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_35 : subd10_4 [1, 1] = true := by decide +kernel
theorem subd10_4_36 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_37 : subd10_4 [1, 3] = true := by decide +kernel
theorem subd10_4_38 : subd10_4 [2, -5] = true := by decide +kernel
theorem subd10_4_39 : subd10_4 [2, -4] = true := by decide +kernel
theorem subd10_4_40 : subd10_4 [2, -3] = true := by decide +kernel
theorem subd10_4_41 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_42 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_43 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_44 : subd10_4 [2, 1] = true := by decide +kernel
theorem subd10_4_45 : subd10_4 [2, 2] = true := by decide +kernel
theorem subd10_4_46 : subd10_4 [2, 3] = true := by decide +kernel
theorem subd10_4_47 : subd10_4 [3] = true := by decide +kernel
theorem sbd10_4_1 : ∀ q ∈ blkd10_4_1, subd10_4 q = true := by
  unfold blkd10_4_1
  exact List.forall_mem_cons.2 ⟨subd10_4_32, List.forall_mem_cons.2 ⟨subd10_4_33, List.forall_mem_cons.2 ⟨subd10_4_34, List.forall_mem_cons.2 ⟨subd10_4_35, List.forall_mem_cons.2 ⟨subd10_4_36, List.forall_mem_cons.2 ⟨subd10_4_37, List.forall_mem_cons.2 ⟨subd10_4_38, List.forall_mem_cons.2 ⟨subd10_4_39, List.forall_mem_cons.2 ⟨subd10_4_40, List.forall_mem_cons.2 ⟨subd10_4_41, List.forall_mem_cons.2 ⟨subd10_4_42, List.forall_mem_cons.2 ⟨subd10_4_43, List.forall_mem_cons.2 ⟨subd10_4_44, List.forall_mem_cons.2 ⟨subd10_4_45, List.forall_mem_cons.2 ⟨subd10_4_46, List.forall_mem_cons.2 ⟨subd10_4_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [0, 0, -7] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [0, 0, -6] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [0, 0, -5] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [0, 0, -4] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [0, 0, -3] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [0, 0, -2] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [0, 0, -1] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [0, 0, 0] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [0, 0, 1] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [0, 0, 2] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [0, 0, 3] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [0, 0, 4] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [0, 0, 5] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [0, 0, 6] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, 1, -6] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, 1, -5] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-2, 1, -4] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-2, 1, -3] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-2, 1, -2] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-2, 1, -1] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-2, 1, 0] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-2, 1, 1] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-2, 1, 2] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-2, 1, 3] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-2, 1, 4] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-2, 1, 5] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-2, 1, 6] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-2, 1, 7] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-1, -1, -8] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-1, -1, -7] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-1, -1, -6] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-1, -1, -5] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-1, -1, -4] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [-1, -1, -3] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [-1, -1, -2] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [-1, -1, -1] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [-1, -1, 0] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [-1, -1, 1] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [-1, -1, 2] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [-1, -1, 3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [-1, -1, 4] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [-1, -1, 5] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [-1, -1, 6] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [-1, -1, 7] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [-1, 0, -9] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [-1, 0, -8] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [-1, 0, -7] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [-1, 0, -6] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [-1, 0, -5] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [-1, 0, -4] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [-1, 0, -3] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [-1, 0, -2] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [-1, 0, -1] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [-1, 0, 0] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [-1, 0, 1] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [-1, 0, 2] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [-1, 0, 3] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [-1, 0, 4] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [-1, 0, 5] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [-1, 0, 6] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [-1, 0, 7] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [-1, 0, 8] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [-1, 1, -8] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [-1, 1, -7] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [-1, 1, -6] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [-1, 1, -5] = true := by decide +kernel
theorem subd11_1_58 : subd11_1 [-1, 1, -4] = true := by decide +kernel
theorem subd11_1_59 : subd11_1 [-1, 1, -3] = true := by decide +kernel
theorem subd11_1_60 : subd11_1 [-1, 1, -2] = true := by decide +kernel
theorem subd11_1_61 : subd11_1 [-1, 1, -1] = true := by decide +kernel
theorem subd11_1_62 : subd11_1 [-1, 1, 0] = true := by decide +kernel
theorem subd11_1_63 : subd11_1 [-1, 1, 1] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_cons.2 ⟨subd11_1_58, List.forall_mem_cons.2 ⟨subd11_1_59, List.forall_mem_cons.2 ⟨subd11_1_60, List.forall_mem_cons.2 ⟨subd11_1_61, List.forall_mem_cons.2 ⟨subd11_1_62, List.forall_mem_cons.2 ⟨subd11_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_64 : subd11_1 [-1, 1, 2] = true := by decide +kernel
theorem subd11_1_65 : subd11_1 [-1, 1, 3] = true := by decide +kernel
theorem subd11_1_66 : subd11_1 [-1, 1, 4] = true := by decide +kernel
theorem subd11_1_67 : subd11_1 [-1, 1, 5] = true := by decide +kernel
theorem subd11_1_68 : subd11_1 [-1, 1, 6] = true := by decide +kernel
theorem subd11_1_69 : subd11_1 [-1, 1, 7] = true := by decide +kernel
theorem subd11_1_70 : subd11_1 [-1, 1, 8] = true := by decide +kernel
theorem subd11_1_71 : subd11_1 [-1, 2, -7] = true := by decide +kernel
theorem subd11_1_72 : subd11_1 [-1, 2, -6] = true := by decide +kernel
theorem subd11_1_73 : subd11_1 [-1, 2, -5] = true := by decide +kernel
theorem subd11_1_74 : subd11_1 [-1, 2, -4] = true := by decide +kernel
theorem subd11_1_75 : subd11_1 [-1, 2, -3] = true := by decide +kernel
theorem subd11_1_76 : subd11_1 [-1, 2, -2] = true := by decide +kernel
theorem subd11_1_77 : subd11_1 [-1, 2, -1] = true := by decide +kernel
theorem subd11_1_78 : subd11_1 [-1, 2, 0] = true := by decide +kernel
theorem subd11_1_79 : subd11_1 [-1, 2, 1] = true := by decide +kernel
theorem subd11_1_80 : subd11_1 [-1, 2, 2] = true := by decide +kernel
theorem subd11_1_81 : subd11_1 [-1, 2, 3] = true := by decide +kernel
theorem subd11_1_82 : subd11_1 [-1, 2, 4] = true := by decide +kernel
theorem subd11_1_83 : subd11_1 [-1, 2, 5] = true := by decide +kernel
theorem subd11_1_84 : subd11_1 [-1, 2, 6] = true := by decide +kernel
theorem subd11_1_85 : subd11_1 [-1, 2, 7] = true := by decide +kernel
theorem subd11_1_86 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_87 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_88 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_89 : subd11_1 [0, -2, -8] = true := by decide +kernel
theorem subd11_1_90 : subd11_1 [0, -2, -7] = true := by decide +kernel
theorem subd11_1_91 : subd11_1 [0, -2, -6] = true := by decide +kernel
theorem subd11_1_92 : subd11_1 [0, -2, -5] = true := by decide +kernel
theorem subd11_1_93 : subd11_1 [0, -2, -4] = true := by decide +kernel
theorem subd11_1_94 : subd11_1 [0, -2, -3] = true := by decide +kernel
theorem subd11_1_95 : subd11_1 [0, -2, -2] = true := by decide +kernel
theorem sbd11_1_2 : ∀ q ∈ blkd11_1_2, subd11_1 q = true := by
  unfold blkd11_1_2
  exact List.forall_mem_cons.2 ⟨subd11_1_64, List.forall_mem_cons.2 ⟨subd11_1_65, List.forall_mem_cons.2 ⟨subd11_1_66, List.forall_mem_cons.2 ⟨subd11_1_67, List.forall_mem_cons.2 ⟨subd11_1_68, List.forall_mem_cons.2 ⟨subd11_1_69, List.forall_mem_cons.2 ⟨subd11_1_70, List.forall_mem_cons.2 ⟨subd11_1_71, List.forall_mem_cons.2 ⟨subd11_1_72, List.forall_mem_cons.2 ⟨subd11_1_73, List.forall_mem_cons.2 ⟨subd11_1_74, List.forall_mem_cons.2 ⟨subd11_1_75, List.forall_mem_cons.2 ⟨subd11_1_76, List.forall_mem_cons.2 ⟨subd11_1_77, List.forall_mem_cons.2 ⟨subd11_1_78, List.forall_mem_cons.2 ⟨subd11_1_79, List.forall_mem_cons.2 ⟨subd11_1_80, List.forall_mem_cons.2 ⟨subd11_1_81, List.forall_mem_cons.2 ⟨subd11_1_82, List.forall_mem_cons.2 ⟨subd11_1_83, List.forall_mem_cons.2 ⟨subd11_1_84, List.forall_mem_cons.2 ⟨subd11_1_85, List.forall_mem_cons.2 ⟨subd11_1_86, List.forall_mem_cons.2 ⟨subd11_1_87, List.forall_mem_cons.2 ⟨subd11_1_88, List.forall_mem_cons.2 ⟨subd11_1_89, List.forall_mem_cons.2 ⟨subd11_1_90, List.forall_mem_cons.2 ⟨subd11_1_91, List.forall_mem_cons.2 ⟨subd11_1_92, List.forall_mem_cons.2 ⟨subd11_1_93, List.forall_mem_cons.2 ⟨subd11_1_94, List.forall_mem_cons.2 ⟨subd11_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_96 : subd11_1 [0, -2, -1] = true := by decide +kernel
theorem subd11_1_97 : subd11_1 [0, -2, 0] = true := by decide +kernel
theorem subd11_1_98 : subd11_1 [0, -2, 1] = true := by decide +kernel
theorem subd11_1_99 : subd11_1 [0, -2, 2] = true := by decide +kernel
theorem subd11_1_100 : subd11_1 [0, -2, 3] = true := by decide +kernel
theorem subd11_1_101 : subd11_1 [0, -2, 4] = true := by decide +kernel
theorem subd11_1_102 : subd11_1 [0, -2, 5] = true := by decide +kernel
theorem subd11_1_103 : subd11_1 [0, -2, 6] = true := by decide +kernel
theorem subd11_1_104 : subd11_1 [0, -1, -9] = true := by decide +kernel
theorem subd11_1_105 : subd11_1 [0, -1, -8] = true := by decide +kernel
theorem subd11_1_106 : subd11_1 [0, -1, -7] = true := by decide +kernel
theorem subd11_1_107 : subd11_1 [0, -1, -6] = true := by decide +kernel
theorem subd11_1_108 : subd11_1 [0, -1, -5] = true := by decide +kernel
theorem subd11_1_109 : subd11_1 [0, -1, -4] = true := by decide +kernel
theorem subd11_1_110 : subd11_1 [0, -1, -3] = true := by decide +kernel
theorem subd11_1_111 : subd11_1 [0, -1, -2] = true := by decide +kernel
theorem subd11_1_112 : subd11_1 [0, -1, -1] = true := by decide +kernel
theorem subd11_1_113 : subd11_1 [0, -1, 0] = true := by decide +kernel
theorem subd11_1_114 : subd11_1 [0, -1, 1] = true := by decide +kernel
theorem subd11_1_115 : subd11_1 [0, -1, 2] = true := by decide +kernel
theorem subd11_1_116 : subd11_1 [0, -1, 3] = true := by decide +kernel
theorem subd11_1_117 : subd11_1 [0, -1, 4] = true := by decide +kernel
theorem subd11_1_118 : subd11_1 [0, -1, 5] = true := by decide +kernel
theorem subd11_1_119 : subd11_1 [0, -1, 6] = true := by decide +kernel
theorem subd11_1_120 : subd11_1 [0, -1, 7] = true := by decide +kernel
theorem subd11_1_121 : subd11_1 [0, -1, 8] = true := by decide +kernel
theorem subd11_1_122 : subd11_1 [0, 0, -9] = true := by decide +kernel
theorem subd11_1_123 : subd11_1 [0, 0, -8] = true := by decide +kernel
theorem subd11_1_124 : subd11_1 [0, 0, -7] = true := by decide +kernel
theorem subd11_1_125 : subd11_1 [0, 0, -6] = true := by decide +kernel
theorem subd11_1_126 : subd11_1 [0, 0, -5] = true := by decide +kernel
theorem subd11_1_127 : subd11_1 [0, 0, -4] = true := by decide +kernel
theorem sbd11_1_3 : ∀ q ∈ blkd11_1_3, subd11_1 q = true := by
  unfold blkd11_1_3
  exact List.forall_mem_cons.2 ⟨subd11_1_96, List.forall_mem_cons.2 ⟨subd11_1_97, List.forall_mem_cons.2 ⟨subd11_1_98, List.forall_mem_cons.2 ⟨subd11_1_99, List.forall_mem_cons.2 ⟨subd11_1_100, List.forall_mem_cons.2 ⟨subd11_1_101, List.forall_mem_cons.2 ⟨subd11_1_102, List.forall_mem_cons.2 ⟨subd11_1_103, List.forall_mem_cons.2 ⟨subd11_1_104, List.forall_mem_cons.2 ⟨subd11_1_105, List.forall_mem_cons.2 ⟨subd11_1_106, List.forall_mem_cons.2 ⟨subd11_1_107, List.forall_mem_cons.2 ⟨subd11_1_108, List.forall_mem_cons.2 ⟨subd11_1_109, List.forall_mem_cons.2 ⟨subd11_1_110, List.forall_mem_cons.2 ⟨subd11_1_111, List.forall_mem_cons.2 ⟨subd11_1_112, List.forall_mem_cons.2 ⟨subd11_1_113, List.forall_mem_cons.2 ⟨subd11_1_114, List.forall_mem_cons.2 ⟨subd11_1_115, List.forall_mem_cons.2 ⟨subd11_1_116, List.forall_mem_cons.2 ⟨subd11_1_117, List.forall_mem_cons.2 ⟨subd11_1_118, List.forall_mem_cons.2 ⟨subd11_1_119, List.forall_mem_cons.2 ⟨subd11_1_120, List.forall_mem_cons.2 ⟨subd11_1_121, List.forall_mem_cons.2 ⟨subd11_1_122, List.forall_mem_cons.2 ⟨subd11_1_123, List.forall_mem_cons.2 ⟨subd11_1_124, List.forall_mem_cons.2 ⟨subd11_1_125, List.forall_mem_cons.2 ⟨subd11_1_126, List.forall_mem_cons.2 ⟨subd11_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_128 : subd11_1 [0, 0, -3] = true := by decide +kernel
theorem subd11_1_129 : subd11_1 [0, 0, -2] = true := by decide +kernel
theorem subd11_1_130 : subd11_1 [0, 0, -1] = true := by decide +kernel
theorem subd11_1_131 : subd11_1 [0, 0, 0] = true := by decide +kernel
theorem subd11_1_132 : subd11_1 [0, 0, 1] = true := by decide +kernel
theorem subd11_1_133 : subd11_1 [0, 0, 2] = true := by decide +kernel
theorem subd11_1_134 : subd11_1 [0, 0, 3] = true := by decide +kernel
theorem subd11_1_135 : subd11_1 [0, 0, 4] = true := by decide +kernel
theorem subd11_1_136 : subd11_1 [0, 0, 5] = true := by decide +kernel
theorem subd11_1_137 : subd11_1 [0, 0, 6] = true := by decide +kernel
theorem subd11_1_138 : subd11_1 [0, 0, 7] = true := by decide +kernel
theorem subd11_1_139 : subd11_1 [0, 0, 8] = true := by decide +kernel
theorem subd11_1_140 : subd11_1 [0, 1, -9] = true := by decide +kernel
theorem subd11_1_141 : subd11_1 [0, 1, -8] = true := by decide +kernel
theorem subd11_1_142 : subd11_1 [0, 1, -7] = true := by decide +kernel
theorem subd11_1_143 : subd11_1 [0, 1, -6] = true := by decide +kernel
theorem subd11_1_144 : subd11_1 [0, 1, -5] = true := by decide +kernel
theorem subd11_1_145 : subd11_1 [0, 1, -4] = true := by decide +kernel
theorem subd11_1_146 : subd11_1 [0, 1, -3] = true := by decide +kernel
theorem subd11_1_147 : subd11_1 [0, 1, -2] = true := by decide +kernel
theorem subd11_1_148 : subd11_1 [0, 1, -1] = true := by decide +kernel
theorem subd11_1_149 : subd11_1 [0, 1, 0] = true := by decide +kernel
theorem subd11_1_150 : subd11_1 [0, 1, 1] = true := by decide +kernel
theorem subd11_1_151 : subd11_1 [0, 1, 2] = true := by decide +kernel
theorem subd11_1_152 : subd11_1 [0, 1, 3] = true := by decide +kernel
theorem subd11_1_153 : subd11_1 [0, 1, 4] = true := by decide +kernel
theorem subd11_1_154 : subd11_1 [0, 1, 5] = true := by decide +kernel
theorem subd11_1_155 : subd11_1 [0, 1, 6] = true := by decide +kernel
theorem subd11_1_156 : subd11_1 [0, 1, 7] = true := by decide +kernel
theorem subd11_1_157 : subd11_1 [0, 1, 8] = true := by decide +kernel
theorem subd11_1_158 : subd11_1 [0, 2, -7] = true := by decide +kernel
theorem subd11_1_159 : subd11_1 [0, 2, -6] = true := by decide +kernel
theorem sbd11_1_4 : ∀ q ∈ blkd11_1_4, subd11_1 q = true := by
  unfold blkd11_1_4
  exact List.forall_mem_cons.2 ⟨subd11_1_128, List.forall_mem_cons.2 ⟨subd11_1_129, List.forall_mem_cons.2 ⟨subd11_1_130, List.forall_mem_cons.2 ⟨subd11_1_131, List.forall_mem_cons.2 ⟨subd11_1_132, List.forall_mem_cons.2 ⟨subd11_1_133, List.forall_mem_cons.2 ⟨subd11_1_134, List.forall_mem_cons.2 ⟨subd11_1_135, List.forall_mem_cons.2 ⟨subd11_1_136, List.forall_mem_cons.2 ⟨subd11_1_137, List.forall_mem_cons.2 ⟨subd11_1_138, List.forall_mem_cons.2 ⟨subd11_1_139, List.forall_mem_cons.2 ⟨subd11_1_140, List.forall_mem_cons.2 ⟨subd11_1_141, List.forall_mem_cons.2 ⟨subd11_1_142, List.forall_mem_cons.2 ⟨subd11_1_143, List.forall_mem_cons.2 ⟨subd11_1_144, List.forall_mem_cons.2 ⟨subd11_1_145, List.forall_mem_cons.2 ⟨subd11_1_146, List.forall_mem_cons.2 ⟨subd11_1_147, List.forall_mem_cons.2 ⟨subd11_1_148, List.forall_mem_cons.2 ⟨subd11_1_149, List.forall_mem_cons.2 ⟨subd11_1_150, List.forall_mem_cons.2 ⟨subd11_1_151, List.forall_mem_cons.2 ⟨subd11_1_152, List.forall_mem_cons.2 ⟨subd11_1_153, List.forall_mem_cons.2 ⟨subd11_1_154, List.forall_mem_cons.2 ⟨subd11_1_155, List.forall_mem_cons.2 ⟨subd11_1_156, List.forall_mem_cons.2 ⟨subd11_1_157, List.forall_mem_cons.2 ⟨subd11_1_158, List.forall_mem_cons.2 ⟨subd11_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_160 : subd11_1 [0, 2, -5] = true := by decide +kernel
theorem subd11_1_161 : subd11_1 [0, 2, -4] = true := by decide +kernel
theorem subd11_1_162 : subd11_1 [0, 2, -3] = true := by decide +kernel
theorem subd11_1_163 : subd11_1 [0, 2, -2] = true := by decide +kernel
theorem subd11_1_164 : subd11_1 [0, 2, -1] = true := by decide +kernel
theorem subd11_1_165 : subd11_1 [0, 2, 0] = true := by decide +kernel
theorem subd11_1_166 : subd11_1 [0, 2, 1] = true := by decide +kernel
theorem subd11_1_167 : subd11_1 [0, 2, 2] = true := by decide +kernel
theorem subd11_1_168 : subd11_1 [0, 2, 3] = true := by decide +kernel
theorem subd11_1_169 : subd11_1 [0, 2, 4] = true := by decide +kernel
theorem subd11_1_170 : subd11_1 [0, 2, 5] = true := by decide +kernel
theorem subd11_1_171 : subd11_1 [0, 2, 6] = true := by decide +kernel
theorem subd11_1_172 : subd11_1 [0, 2, 7] = true := by decide +kernel
theorem subd11_1_173 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_174 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_175 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_176 : subd11_1 [1, -2, -8] = true := by decide +kernel
theorem subd11_1_177 : subd11_1 [1, -2, -7] = true := by decide +kernel
theorem subd11_1_178 : subd11_1 [1, -2, -6] = true := by decide +kernel
theorem subd11_1_179 : subd11_1 [1, -2, -5] = true := by decide +kernel
theorem subd11_1_180 : subd11_1 [1, -2, -4] = true := by decide +kernel
theorem subd11_1_181 : subd11_1 [1, -2, -3] = true := by decide +kernel
theorem subd11_1_182 : subd11_1 [1, -2, -2] = true := by decide +kernel
theorem subd11_1_183 : subd11_1 [1, -2, -1] = true := by decide +kernel
theorem subd11_1_184 : subd11_1 [1, -2, 0] = true := by decide +kernel
theorem subd11_1_185 : subd11_1 [1, -2, 1] = true := by decide +kernel
theorem subd11_1_186 : subd11_1 [1, -2, 2] = true := by decide +kernel
theorem subd11_1_187 : subd11_1 [1, -2, 3] = true := by decide +kernel
theorem subd11_1_188 : subd11_1 [1, -2, 4] = true := by decide +kernel
theorem subd11_1_189 : subd11_1 [1, -2, 5] = true := by decide +kernel
theorem subd11_1_190 : subd11_1 [1, -2, 6] = true := by decide +kernel
theorem subd11_1_191 : subd11_1 [1, -1, -9] = true := by decide +kernel
theorem sbd11_1_5 : ∀ q ∈ blkd11_1_5, subd11_1 q = true := by
  unfold blkd11_1_5
  exact List.forall_mem_cons.2 ⟨subd11_1_160, List.forall_mem_cons.2 ⟨subd11_1_161, List.forall_mem_cons.2 ⟨subd11_1_162, List.forall_mem_cons.2 ⟨subd11_1_163, List.forall_mem_cons.2 ⟨subd11_1_164, List.forall_mem_cons.2 ⟨subd11_1_165, List.forall_mem_cons.2 ⟨subd11_1_166, List.forall_mem_cons.2 ⟨subd11_1_167, List.forall_mem_cons.2 ⟨subd11_1_168, List.forall_mem_cons.2 ⟨subd11_1_169, List.forall_mem_cons.2 ⟨subd11_1_170, List.forall_mem_cons.2 ⟨subd11_1_171, List.forall_mem_cons.2 ⟨subd11_1_172, List.forall_mem_cons.2 ⟨subd11_1_173, List.forall_mem_cons.2 ⟨subd11_1_174, List.forall_mem_cons.2 ⟨subd11_1_175, List.forall_mem_cons.2 ⟨subd11_1_176, List.forall_mem_cons.2 ⟨subd11_1_177, List.forall_mem_cons.2 ⟨subd11_1_178, List.forall_mem_cons.2 ⟨subd11_1_179, List.forall_mem_cons.2 ⟨subd11_1_180, List.forall_mem_cons.2 ⟨subd11_1_181, List.forall_mem_cons.2 ⟨subd11_1_182, List.forall_mem_cons.2 ⟨subd11_1_183, List.forall_mem_cons.2 ⟨subd11_1_184, List.forall_mem_cons.2 ⟨subd11_1_185, List.forall_mem_cons.2 ⟨subd11_1_186, List.forall_mem_cons.2 ⟨subd11_1_187, List.forall_mem_cons.2 ⟨subd11_1_188, List.forall_mem_cons.2 ⟨subd11_1_189, List.forall_mem_cons.2 ⟨subd11_1_190, List.forall_mem_cons.2 ⟨subd11_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_192 : subd11_1 [1, -1, -8] = true := by decide +kernel
theorem subd11_1_193 : subd11_1 [1, -1, -7] = true := by decide +kernel
theorem subd11_1_194 : subd11_1 [1, -1, -6] = true := by decide +kernel
theorem subd11_1_195 : subd11_1 [1, -1, -5] = true := by decide +kernel
theorem subd11_1_196 : subd11_1 [1, -1, -4] = true := by decide +kernel
theorem subd11_1_197 : subd11_1 [1, -1, -3] = true := by decide +kernel
theorem subd11_1_198 : subd11_1 [1, -1, -2] = true := by decide +kernel
theorem subd11_1_199 : subd11_1 [1, -1, -1] = true := by decide +kernel
theorem subd11_1_200 : subd11_1 [1, -1, 0] = true := by decide +kernel
theorem subd11_1_201 : subd11_1 [1, -1, 1] = true := by decide +kernel
theorem subd11_1_202 : subd11_1 [1, -1, 2] = true := by decide +kernel
theorem subd11_1_203 : subd11_1 [1, -1, 3] = true := by decide +kernel
theorem subd11_1_204 : subd11_1 [1, -1, 4] = true := by decide +kernel
theorem subd11_1_205 : subd11_1 [1, -1, 5] = true := by decide +kernel
theorem subd11_1_206 : subd11_1 [1, -1, 6] = true := by decide +kernel
theorem subd11_1_207 : subd11_1 [1, -1, 7] = true := by decide +kernel
theorem subd11_1_208 : subd11_1 [1, 0, -9] = true := by decide +kernel
theorem subd11_1_209 : subd11_1 [1, 0, -8] = true := by decide +kernel
theorem subd11_1_210 : subd11_1 [1, 0, -7] = true := by decide +kernel
theorem subd11_1_211 : subd11_1 [1, 0, -6] = true := by decide +kernel
theorem subd11_1_212 : subd11_1 [1, 0, -5] = true := by decide +kernel
theorem subd11_1_213 : subd11_1 [1, 0, -4] = true := by decide +kernel
theorem subd11_1_214 : subd11_1 [1, 0, -3] = true := by decide +kernel
theorem subd11_1_215 : subd11_1 [1, 0, -2] = true := by decide +kernel
theorem subd11_1_216 : subd11_1 [1, 0, -1] = true := by decide +kernel
theorem subd11_1_217 : subd11_1 [1, 0, 0] = true := by decide +kernel
theorem subd11_1_218 : subd11_1 [1, 0, 1] = true := by decide +kernel
theorem subd11_1_219 : subd11_1 [1, 0, 2] = true := by decide +kernel
theorem subd11_1_220 : subd11_1 [1, 0, 3] = true := by decide +kernel
theorem subd11_1_221 : subd11_1 [1, 0, 4] = true := by decide +kernel
theorem subd11_1_222 : subd11_1 [1, 0, 5] = true := by decide +kernel
theorem subd11_1_223 : subd11_1 [1, 0, 6] = true := by decide +kernel
theorem sbd11_1_6 : ∀ q ∈ blkd11_1_6, subd11_1 q = true := by
  unfold blkd11_1_6
  exact List.forall_mem_cons.2 ⟨subd11_1_192, List.forall_mem_cons.2 ⟨subd11_1_193, List.forall_mem_cons.2 ⟨subd11_1_194, List.forall_mem_cons.2 ⟨subd11_1_195, List.forall_mem_cons.2 ⟨subd11_1_196, List.forall_mem_cons.2 ⟨subd11_1_197, List.forall_mem_cons.2 ⟨subd11_1_198, List.forall_mem_cons.2 ⟨subd11_1_199, List.forall_mem_cons.2 ⟨subd11_1_200, List.forall_mem_cons.2 ⟨subd11_1_201, List.forall_mem_cons.2 ⟨subd11_1_202, List.forall_mem_cons.2 ⟨subd11_1_203, List.forall_mem_cons.2 ⟨subd11_1_204, List.forall_mem_cons.2 ⟨subd11_1_205, List.forall_mem_cons.2 ⟨subd11_1_206, List.forall_mem_cons.2 ⟨subd11_1_207, List.forall_mem_cons.2 ⟨subd11_1_208, List.forall_mem_cons.2 ⟨subd11_1_209, List.forall_mem_cons.2 ⟨subd11_1_210, List.forall_mem_cons.2 ⟨subd11_1_211, List.forall_mem_cons.2 ⟨subd11_1_212, List.forall_mem_cons.2 ⟨subd11_1_213, List.forall_mem_cons.2 ⟨subd11_1_214, List.forall_mem_cons.2 ⟨subd11_1_215, List.forall_mem_cons.2 ⟨subd11_1_216, List.forall_mem_cons.2 ⟨subd11_1_217, List.forall_mem_cons.2 ⟨subd11_1_218, List.forall_mem_cons.2 ⟨subd11_1_219, List.forall_mem_cons.2 ⟨subd11_1_220, List.forall_mem_cons.2 ⟨subd11_1_221, List.forall_mem_cons.2 ⟨subd11_1_222, List.forall_mem_cons.2 ⟨subd11_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_224 : subd11_1 [1, 0, 7] = true := by decide +kernel
theorem subd11_1_225 : subd11_1 [1, 0, 8] = true := by decide +kernel
theorem subd11_1_226 : subd11_1 [1, 1, -8] = true := by decide +kernel
theorem subd11_1_227 : subd11_1 [1, 1, -7] = true := by decide +kernel
theorem subd11_1_228 : subd11_1 [1, 1, -6] = true := by decide +kernel
theorem subd11_1_229 : subd11_1 [1, 1, -5] = true := by decide +kernel
theorem subd11_1_230 : subd11_1 [1, 1, -4] = true := by decide +kernel
theorem subd11_1_231 : subd11_1 [1, 1, -3] = true := by decide +kernel
theorem subd11_1_232 : subd11_1 [1, 1, -2] = true := by decide +kernel
theorem subd11_1_233 : subd11_1 [1, 1, -1] = true := by decide +kernel
theorem subd11_1_234 : subd11_1 [1, 1, 0] = true := by decide +kernel
theorem subd11_1_235 : subd11_1 [1, 1, 1] = true := by decide +kernel
theorem subd11_1_236 : subd11_1 [1, 1, 2] = true := by decide +kernel
theorem subd11_1_237 : subd11_1 [1, 1, 3] = true := by decide +kernel
theorem subd11_1_238 : subd11_1 [1, 1, 4] = true := by decide +kernel
theorem subd11_1_239 : subd11_1 [1, 1, 5] = true := by decide +kernel
theorem subd11_1_240 : subd11_1 [1, 1, 6] = true := by decide +kernel
theorem subd11_1_241 : subd11_1 [1, 1, 7] = true := by decide +kernel
theorem subd11_1_242 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_243 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_244 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_245 : subd11_1 [2, -1, -8] = true := by decide +kernel
theorem subd11_1_246 : subd11_1 [2, -1, -7] = true := by decide +kernel
theorem subd11_1_247 : subd11_1 [2, -1, -6] = true := by decide +kernel
theorem subd11_1_248 : subd11_1 [2, -1, -5] = true := by decide +kernel
theorem subd11_1_249 : subd11_1 [2, -1, -4] = true := by decide +kernel
theorem subd11_1_250 : subd11_1 [2, -1, -3] = true := by decide +kernel
theorem subd11_1_251 : subd11_1 [2, -1, -2] = true := by decide +kernel
theorem subd11_1_252 : subd11_1 [2, -1, -1] = true := by decide +kernel
theorem subd11_1_253 : subd11_1 [2, -1, 0] = true := by decide +kernel
theorem subd11_1_254 : subd11_1 [2, -1, 1] = true := by decide +kernel
theorem subd11_1_255 : subd11_1 [2, -1, 2] = true := by decide +kernel
theorem sbd11_1_7 : ∀ q ∈ blkd11_1_7, subd11_1 q = true := by
  unfold blkd11_1_7
  exact List.forall_mem_cons.2 ⟨subd11_1_224, List.forall_mem_cons.2 ⟨subd11_1_225, List.forall_mem_cons.2 ⟨subd11_1_226, List.forall_mem_cons.2 ⟨subd11_1_227, List.forall_mem_cons.2 ⟨subd11_1_228, List.forall_mem_cons.2 ⟨subd11_1_229, List.forall_mem_cons.2 ⟨subd11_1_230, List.forall_mem_cons.2 ⟨subd11_1_231, List.forall_mem_cons.2 ⟨subd11_1_232, List.forall_mem_cons.2 ⟨subd11_1_233, List.forall_mem_cons.2 ⟨subd11_1_234, List.forall_mem_cons.2 ⟨subd11_1_235, List.forall_mem_cons.2 ⟨subd11_1_236, List.forall_mem_cons.2 ⟨subd11_1_237, List.forall_mem_cons.2 ⟨subd11_1_238, List.forall_mem_cons.2 ⟨subd11_1_239, List.forall_mem_cons.2 ⟨subd11_1_240, List.forall_mem_cons.2 ⟨subd11_1_241, List.forall_mem_cons.2 ⟨subd11_1_242, List.forall_mem_cons.2 ⟨subd11_1_243, List.forall_mem_cons.2 ⟨subd11_1_244, List.forall_mem_cons.2 ⟨subd11_1_245, List.forall_mem_cons.2 ⟨subd11_1_246, List.forall_mem_cons.2 ⟨subd11_1_247, List.forall_mem_cons.2 ⟨subd11_1_248, List.forall_mem_cons.2 ⟨subd11_1_249, List.forall_mem_cons.2 ⟨subd11_1_250, List.forall_mem_cons.2 ⟨subd11_1_251, List.forall_mem_cons.2 ⟨subd11_1_252, List.forall_mem_cons.2 ⟨subd11_1_253, List.forall_mem_cons.2 ⟨subd11_1_254, List.forall_mem_cons.2 ⟨subd11_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_256 : subd11_1 [2, -1, 3] = true := by decide +kernel
theorem subd11_1_257 : subd11_1 [2, -1, 4] = true := by decide +kernel
theorem subd11_1_258 : subd11_1 [2, -1, 5] = true := by decide +kernel
theorem subd11_1_259 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_260 : subd11_1 [2, 1] = true := by decide +kernel
theorem sbd11_1_8 : ∀ q ∈ blkd11_1_8, subd11_1 q = true := by
  unfold blkd11_1_8
  exact List.forall_mem_cons.2 ⟨subd11_1_256, List.forall_mem_cons.2 ⟨subd11_1_257, List.forall_mem_cons.2 ⟨subd11_1_258, List.forall_mem_cons.2 ⟨subd11_1_259, List.forall_mem_cons.2 ⟨subd11_1_260, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
