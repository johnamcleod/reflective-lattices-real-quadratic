import ReflectZphi.Data.Cert5.C095.Base

namespace ReflectZphi.Data.Cert5.C095

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_32 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [2, -1] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [2, 0] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [2, 1] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [2, 2] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [3] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_0 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [1] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [1] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_0 : subd10_4 [] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_nil _⟩
theorem subd10_5_0 : subd10_5 [] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_nil _⟩
theorem subd10_6_0 : subd10_6 [] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_nil _⟩
theorem subd11_0_0 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-1, 0, -7] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-1, 0, -6] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-1, 0, -5] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-1, 0, -4] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-1, 0, -3] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-1, 0, -2] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-1, 0, -1] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-1, 0, 0] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-1, 0, 1] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-1, 0, 2] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-1, 0, 3] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-1, 0, 4] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-1, 0, 5] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-1, 0, 6] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-1, 1, -7] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-1, 1, -6] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-1, 1, -5] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-1, 1, -4] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-1, 1, -3] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-1, 1, -2] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-1, 1, -1] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-1, 1, 0] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-1, 1, 1] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-1, 1, 2] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-1, 1, 3] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-1, 1, 4] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [-1, 1, 5] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [-1, 1, 6] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [0, -3] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [0, -1, -8] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [0, -1, -7] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [0, -1, -6] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [0, -1, -5] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [0, -1, -4] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [0, -1, -3] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [0, -1, -2] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [0, -1, -1] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [0, -1, 0] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [0, -1, 1] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [0, -1, 2] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [0, -1, 3] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [0, -1, 4] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [0, -1, 5] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [0, -1, 6] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [0, 0, -8] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [0, 0, -7] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [0, 0, -6] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [0, 0, -5] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [0, 0, -4] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [0, 0, -3] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [0, 0, -2] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [0, 0, -1] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [0, 0, 0] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [0, 0, 1] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [0, 0, 2] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [0, 0, 3] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [0, 0, 4] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [0, 0, 5] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [0, 0, 6] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [0, 0, 7] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [0, 1, -7] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [0, 1, -6] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [0, 1, -5] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [0, 1, -4] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [0, 1, -3] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [0, 1, -2] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [0, 1, -1] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [0, 1, 0] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [0, 1, 1] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [0, 1, 2] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [0, 1, 3] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [0, 1, 4] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [0, 1, 5] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [0, 1, 6] = true := by decide +kernel
theorem subd11_0_78 : subd11_0 [0, 1, 7] = true := by decide +kernel
theorem subd11_0_79 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_80 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_81 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_82 : subd11_0 [1, -1, -7] = true := by decide +kernel
theorem subd11_0_83 : subd11_0 [1, -1, -6] = true := by decide +kernel
theorem subd11_0_84 : subd11_0 [1, -1, -5] = true := by decide +kernel
theorem subd11_0_85 : subd11_0 [1, -1, -4] = true := by decide +kernel
theorem subd11_0_86 : subd11_0 [1, -1, -3] = true := by decide +kernel
theorem subd11_0_87 : subd11_0 [1, -1, -2] = true := by decide +kernel
theorem subd11_0_88 : subd11_0 [1, -1, -1] = true := by decide +kernel
theorem subd11_0_89 : subd11_0 [1, -1, 0] = true := by decide +kernel
theorem subd11_0_90 : subd11_0 [1, -1, 1] = true := by decide +kernel
theorem subd11_0_91 : subd11_0 [1, -1, 2] = true := by decide +kernel
theorem subd11_0_92 : subd11_0 [1, -1, 3] = true := by decide +kernel
theorem subd11_0_93 : subd11_0 [1, -1, 4] = true := by decide +kernel
theorem subd11_0_94 : subd11_0 [1, -1, 5] = true := by decide +kernel
theorem subd11_0_95 : subd11_0 [1, -1, 6] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_cons.2 ⟨subd11_0_78, List.forall_mem_cons.2 ⟨subd11_0_79, List.forall_mem_cons.2 ⟨subd11_0_80, List.forall_mem_cons.2 ⟨subd11_0_81, List.forall_mem_cons.2 ⟨subd11_0_82, List.forall_mem_cons.2 ⟨subd11_0_83, List.forall_mem_cons.2 ⟨subd11_0_84, List.forall_mem_cons.2 ⟨subd11_0_85, List.forall_mem_cons.2 ⟨subd11_0_86, List.forall_mem_cons.2 ⟨subd11_0_87, List.forall_mem_cons.2 ⟨subd11_0_88, List.forall_mem_cons.2 ⟨subd11_0_89, List.forall_mem_cons.2 ⟨subd11_0_90, List.forall_mem_cons.2 ⟨subd11_0_91, List.forall_mem_cons.2 ⟨subd11_0_92, List.forall_mem_cons.2 ⟨subd11_0_93, List.forall_mem_cons.2 ⟨subd11_0_94, List.forall_mem_cons.2 ⟨subd11_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_96 : subd11_0 [1, 0, -7] = true := by decide +kernel
theorem subd11_0_97 : subd11_0 [1, 0, -6] = true := by decide +kernel
theorem subd11_0_98 : subd11_0 [1, 0, -5] = true := by decide +kernel
theorem subd11_0_99 : subd11_0 [1, 0, -4] = true := by decide +kernel
theorem subd11_0_100 : subd11_0 [1, 0, -3] = true := by decide +kernel
theorem subd11_0_101 : subd11_0 [1, 0, -2] = true := by decide +kernel
theorem subd11_0_102 : subd11_0 [1, 0, -1] = true := by decide +kernel
theorem subd11_0_103 : subd11_0 [1, 0, 0] = true := by decide +kernel
theorem subd11_0_104 : subd11_0 [1, 0, 1] = true := by decide +kernel
theorem subd11_0_105 : subd11_0 [1, 0, 2] = true := by decide +kernel
theorem subd11_0_106 : subd11_0 [1, 0, 3] = true := by decide +kernel
theorem subd11_0_107 : subd11_0 [1, 0, 4] = true := by decide +kernel
theorem subd11_0_108 : subd11_0 [1, 0, 5] = true := by decide +kernel
theorem subd11_0_109 : subd11_0 [1, 0, 6] = true := by decide +kernel
theorem subd11_0_110 : subd11_0 [1, 1] = true := by decide +kernel
theorem sbd11_0_3 : ∀ q ∈ blkd11_0_3, subd11_0 q = true := by
  unfold blkd11_0_3
  exact List.forall_mem_cons.2 ⟨subd11_0_96, List.forall_mem_cons.2 ⟨subd11_0_97, List.forall_mem_cons.2 ⟨subd11_0_98, List.forall_mem_cons.2 ⟨subd11_0_99, List.forall_mem_cons.2 ⟨subd11_0_100, List.forall_mem_cons.2 ⟨subd11_0_101, List.forall_mem_cons.2 ⟨subd11_0_102, List.forall_mem_cons.2 ⟨subd11_0_103, List.forall_mem_cons.2 ⟨subd11_0_104, List.forall_mem_cons.2 ⟨subd11_0_105, List.forall_mem_cons.2 ⟨subd11_0_106, List.forall_mem_cons.2 ⟨subd11_0_107, List.forall_mem_cons.2 ⟨subd11_0_108, List.forall_mem_cons.2 ⟨subd11_0_109, List.forall_mem_cons.2 ⟨subd11_0_110, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_0 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [2, 2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [1] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_0 : subd11_3 [-2] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-1] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [1] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_0 : subd11_4 [-1] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [0] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [1] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_nil _⟩⟩⟩
theorem subd11_5_0 : subd11_5 [] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_nil _⟩
theorem subd11_6_0 : subd11_6 [] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C095
