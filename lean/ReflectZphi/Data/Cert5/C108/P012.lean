import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-2] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-1, -2] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [-1, -1] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [-1, 0, -8] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [-1, 0, -7] = true := by decide +kernel
theorem subd9_4_5 : subd9_4 [-1, 0, -6] = true := by decide +kernel
theorem subd9_4_6 : subd9_4 [-1, 0, -5] = true := by decide +kernel
theorem subd9_4_7 : subd9_4 [-1, 0, -4] = true := by decide +kernel
theorem subd9_4_8 : subd9_4 [-1, 0, -3] = true := by decide +kernel
theorem subd9_4_9 : subd9_4 [-1, 0, -2] = true := by decide +kernel
theorem subd9_4_10 : subd9_4 [-1, 0, -1] = true := by decide +kernel
theorem subd9_4_11 : subd9_4 [-1, 0, 0] = true := by decide +kernel
theorem subd9_4_12 : subd9_4 [-1, 0, 1] = true := by decide +kernel
theorem subd9_4_13 : subd9_4 [-1, 0, 2] = true := by decide +kernel
theorem subd9_4_14 : subd9_4 [-1, 0, 3] = true := by decide +kernel
theorem subd9_4_15 : subd9_4 [-1, 0, 4] = true := by decide +kernel
theorem subd9_4_16 : subd9_4 [-1, 0, 5] = true := by decide +kernel
theorem subd9_4_17 : subd9_4 [-1, 0, 6] = true := by decide +kernel
theorem subd9_4_18 : subd9_4 [-1, 1] = true := by decide +kernel
theorem subd9_4_19 : subd9_4 [0, -3] = true := by decide +kernel
theorem subd9_4_20 : subd9_4 [0, -2] = true := by decide +kernel
theorem subd9_4_21 : subd9_4 [0, -1, -7] = true := by decide +kernel
theorem subd9_4_22 : subd9_4 [0, -1, -6] = true := by decide +kernel
theorem subd9_4_23 : subd9_4 [0, -1, -5] = true := by decide +kernel
theorem subd9_4_24 : subd9_4 [0, -1, -4] = true := by decide +kernel
theorem subd9_4_25 : subd9_4 [0, -1, -3] = true := by decide +kernel
theorem subd9_4_26 : subd9_4 [0, -1, -2] = true := by decide +kernel
theorem subd9_4_27 : subd9_4 [0, -1, -1] = true := by decide +kernel
theorem subd9_4_28 : subd9_4 [0, -1, 0] = true := by decide +kernel
theorem subd9_4_29 : subd9_4 [0, -1, 1] = true := by decide +kernel
theorem subd9_4_30 : subd9_4 [0, -1, 2] = true := by decide +kernel
theorem subd9_4_31 : subd9_4 [0, -1, 3] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_cons.2 ⟨subd9_4_5, List.forall_mem_cons.2 ⟨subd9_4_6, List.forall_mem_cons.2 ⟨subd9_4_7, List.forall_mem_cons.2 ⟨subd9_4_8, List.forall_mem_cons.2 ⟨subd9_4_9, List.forall_mem_cons.2 ⟨subd9_4_10, List.forall_mem_cons.2 ⟨subd9_4_11, List.forall_mem_cons.2 ⟨subd9_4_12, List.forall_mem_cons.2 ⟨subd9_4_13, List.forall_mem_cons.2 ⟨subd9_4_14, List.forall_mem_cons.2 ⟨subd9_4_15, List.forall_mem_cons.2 ⟨subd9_4_16, List.forall_mem_cons.2 ⟨subd9_4_17, List.forall_mem_cons.2 ⟨subd9_4_18, List.forall_mem_cons.2 ⟨subd9_4_19, List.forall_mem_cons.2 ⟨subd9_4_20, List.forall_mem_cons.2 ⟨subd9_4_21, List.forall_mem_cons.2 ⟨subd9_4_22, List.forall_mem_cons.2 ⟨subd9_4_23, List.forall_mem_cons.2 ⟨subd9_4_24, List.forall_mem_cons.2 ⟨subd9_4_25, List.forall_mem_cons.2 ⟨subd9_4_26, List.forall_mem_cons.2 ⟨subd9_4_27, List.forall_mem_cons.2 ⟨subd9_4_28, List.forall_mem_cons.2 ⟨subd9_4_29, List.forall_mem_cons.2 ⟨subd9_4_30, List.forall_mem_cons.2 ⟨subd9_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_32 : subd9_4 [0, -1, 4] = true := by decide +kernel
theorem subd9_4_33 : subd9_4 [0, -1, 5] = true := by decide +kernel
theorem subd9_4_34 : subd9_4 [0, -1, 6] = true := by decide +kernel
theorem subd9_4_35 : subd9_4 [0, -1, 7] = true := by decide +kernel
theorem subd9_4_36 : subd9_4 [0, 0, -8] = true := by decide +kernel
theorem subd9_4_37 : subd9_4 [0, 0, -7] = true := by decide +kernel
theorem subd9_4_38 : subd9_4 [0, 0, -6] = true := by decide +kernel
theorem subd9_4_39 : subd9_4 [0, 0, -5] = true := by decide +kernel
theorem subd9_4_40 : subd9_4 [0, 0, -4] = true := by decide +kernel
theorem subd9_4_41 : subd9_4 [0, 0, -3] = true := by decide +kernel
theorem subd9_4_42 : subd9_4 [0, 0, -2] = true := by decide +kernel
theorem subd9_4_43 : subd9_4 [0, 0, -1] = true := by decide +kernel
theorem subd9_4_44 : subd9_4 [0, 0, 0] = true := by decide +kernel
theorem subd9_4_45 : subd9_4 [0, 0, 1] = true := by decide +kernel
theorem subd9_4_46 : subd9_4 [0, 0, 2] = true := by decide +kernel
theorem subd9_4_47 : subd9_4 [0, 0, 3] = true := by decide +kernel
theorem subd9_4_48 : subd9_4 [0, 0, 4] = true := by decide +kernel
theorem subd9_4_49 : subd9_4 [0, 0, 5] = true := by decide +kernel
theorem subd9_4_50 : subd9_4 [0, 0, 6] = true := by decide +kernel
theorem subd9_4_51 : subd9_4 [0, 0, 7] = true := by decide +kernel
theorem subd9_4_52 : subd9_4 [0, 1, -8] = true := by decide +kernel
theorem subd9_4_53 : subd9_4 [0, 1, -7] = true := by decide +kernel
theorem subd9_4_54 : subd9_4 [0, 1, -6] = true := by decide +kernel
theorem subd9_4_55 : subd9_4 [0, 1, -5] = true := by decide +kernel
theorem subd9_4_56 : subd9_4 [0, 1, -4] = true := by decide +kernel
theorem subd9_4_57 : subd9_4 [0, 1, -3] = true := by decide +kernel
theorem subd9_4_58 : subd9_4 [0, 1, -2] = true := by decide +kernel
theorem subd9_4_59 : subd9_4 [0, 1, -1] = true := by decide +kernel
theorem subd9_4_60 : subd9_4 [0, 1, 0] = true := by decide +kernel
theorem subd9_4_61 : subd9_4 [0, 1, 1] = true := by decide +kernel
theorem subd9_4_62 : subd9_4 [0, 1, 2] = true := by decide +kernel
theorem subd9_4_63 : subd9_4 [0, 1, 3] = true := by decide +kernel
theorem sbd9_4_1 : ∀ q ∈ blkd9_4_1, subd9_4 q = true := by
  unfold blkd9_4_1
  exact List.forall_mem_cons.2 ⟨subd9_4_32, List.forall_mem_cons.2 ⟨subd9_4_33, List.forall_mem_cons.2 ⟨subd9_4_34, List.forall_mem_cons.2 ⟨subd9_4_35, List.forall_mem_cons.2 ⟨subd9_4_36, List.forall_mem_cons.2 ⟨subd9_4_37, List.forall_mem_cons.2 ⟨subd9_4_38, List.forall_mem_cons.2 ⟨subd9_4_39, List.forall_mem_cons.2 ⟨subd9_4_40, List.forall_mem_cons.2 ⟨subd9_4_41, List.forall_mem_cons.2 ⟨subd9_4_42, List.forall_mem_cons.2 ⟨subd9_4_43, List.forall_mem_cons.2 ⟨subd9_4_44, List.forall_mem_cons.2 ⟨subd9_4_45, List.forall_mem_cons.2 ⟨subd9_4_46, List.forall_mem_cons.2 ⟨subd9_4_47, List.forall_mem_cons.2 ⟨subd9_4_48, List.forall_mem_cons.2 ⟨subd9_4_49, List.forall_mem_cons.2 ⟨subd9_4_50, List.forall_mem_cons.2 ⟨subd9_4_51, List.forall_mem_cons.2 ⟨subd9_4_52, List.forall_mem_cons.2 ⟨subd9_4_53, List.forall_mem_cons.2 ⟨subd9_4_54, List.forall_mem_cons.2 ⟨subd9_4_55, List.forall_mem_cons.2 ⟨subd9_4_56, List.forall_mem_cons.2 ⟨subd9_4_57, List.forall_mem_cons.2 ⟨subd9_4_58, List.forall_mem_cons.2 ⟨subd9_4_59, List.forall_mem_cons.2 ⟨subd9_4_60, List.forall_mem_cons.2 ⟨subd9_4_61, List.forall_mem_cons.2 ⟨subd9_4_62, List.forall_mem_cons.2 ⟨subd9_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_64 : subd9_4 [0, 1, 4] = true := by decide +kernel
theorem subd9_4_65 : subd9_4 [0, 1, 5] = true := by decide +kernel
theorem subd9_4_66 : subd9_4 [0, 1, 6] = true := by decide +kernel
theorem subd9_4_67 : subd9_4 [0, 2] = true := by decide +kernel
theorem subd9_4_68 : subd9_4 [1, -2] = true := by decide +kernel
theorem subd9_4_69 : subd9_4 [1, -1] = true := by decide +kernel
theorem subd9_4_70 : subd9_4 [1, 0, -7] = true := by decide +kernel
theorem subd9_4_71 : subd9_4 [1, 0, -6] = true := by decide +kernel
theorem subd9_4_72 : subd9_4 [1, 0, -5] = true := by decide +kernel
theorem subd9_4_73 : subd9_4 [1, 0, -4] = true := by decide +kernel
theorem subd9_4_74 : subd9_4 [1, 0, -3] = true := by decide +kernel
theorem subd9_4_75 : subd9_4 [1, 0, -2] = true := by decide +kernel
theorem subd9_4_76 : subd9_4 [1, 0, -1] = true := by decide +kernel
theorem subd9_4_77 : subd9_4 [1, 0, 0] = true := by decide +kernel
theorem subd9_4_78 : subd9_4 [1, 0, 1] = true := by decide +kernel
theorem subd9_4_79 : subd9_4 [1, 0, 2] = true := by decide +kernel
theorem subd9_4_80 : subd9_4 [1, 0, 3] = true := by decide +kernel
theorem subd9_4_81 : subd9_4 [1, 0, 4] = true := by decide +kernel
theorem subd9_4_82 : subd9_4 [1, 0, 5] = true := by decide +kernel
theorem subd9_4_83 : subd9_4 [1, 0, 6] = true := by decide +kernel
theorem subd9_4_84 : subd9_4 [1, 0, 7] = true := by decide +kernel
theorem subd9_4_85 : subd9_4 [1, 1] = true := by decide +kernel
theorem subd9_4_86 : subd9_4 [2] = true := by decide +kernel
theorem sbd9_4_2 : ∀ q ∈ blkd9_4_2, subd9_4 q = true := by
  unfold blkd9_4_2
  exact List.forall_mem_cons.2 ⟨subd9_4_64, List.forall_mem_cons.2 ⟨subd9_4_65, List.forall_mem_cons.2 ⟨subd9_4_66, List.forall_mem_cons.2 ⟨subd9_4_67, List.forall_mem_cons.2 ⟨subd9_4_68, List.forall_mem_cons.2 ⟨subd9_4_69, List.forall_mem_cons.2 ⟨subd9_4_70, List.forall_mem_cons.2 ⟨subd9_4_71, List.forall_mem_cons.2 ⟨subd9_4_72, List.forall_mem_cons.2 ⟨subd9_4_73, List.forall_mem_cons.2 ⟨subd9_4_74, List.forall_mem_cons.2 ⟨subd9_4_75, List.forall_mem_cons.2 ⟨subd9_4_76, List.forall_mem_cons.2 ⟨subd9_4_77, List.forall_mem_cons.2 ⟨subd9_4_78, List.forall_mem_cons.2 ⟨subd9_4_79, List.forall_mem_cons.2 ⟨subd9_4_80, List.forall_mem_cons.2 ⟨subd9_4_81, List.forall_mem_cons.2 ⟨subd9_4_82, List.forall_mem_cons.2 ⟨subd9_4_83, List.forall_mem_cons.2 ⟨subd9_4_84, List.forall_mem_cons.2 ⟨subd9_4_85, List.forall_mem_cons.2 ⟨subd9_4_86, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-2] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-1, -4] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [-1, -3] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [-1, -2] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [-1, -1] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [-1, 0] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [-1, 1] = true := by decide +kernel
theorem subd9_5_7 : subd9_5 [-1, 2] = true := by decide +kernel
theorem subd9_5_8 : subd9_5 [-1, 3] = true := by decide +kernel
theorem subd9_5_9 : subd9_5 [0, -4] = true := by decide +kernel
theorem subd9_5_10 : subd9_5 [0, -3] = true := by decide +kernel
theorem subd9_5_11 : subd9_5 [0, -2] = true := by decide +kernel
theorem subd9_5_12 : subd9_5 [0, -1] = true := by decide +kernel
theorem subd9_5_13 : subd9_5 [0, 0] = true := by decide +kernel
theorem subd9_5_14 : subd9_5 [0, 1] = true := by decide +kernel
theorem subd9_5_15 : subd9_5 [0, 2] = true := by decide +kernel
theorem subd9_5_16 : subd9_5 [0, 3] = true := by decide +kernel
theorem subd9_5_17 : subd9_5 [1, -4] = true := by decide +kernel
theorem subd9_5_18 : subd9_5 [1, -3] = true := by decide +kernel
theorem subd9_5_19 : subd9_5 [1, -2] = true := by decide +kernel
theorem subd9_5_20 : subd9_5 [1, -1] = true := by decide +kernel
theorem subd9_5_21 : subd9_5 [1, 0] = true := by decide +kernel
theorem subd9_5_22 : subd9_5 [1, 1] = true := by decide +kernel
theorem subd9_5_23 : subd9_5 [1, 2] = true := by decide +kernel
theorem subd9_5_24 : subd9_5 [1, 3] = true := by decide +kernel
theorem subd9_5_25 : subd9_5 [2] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_cons.2 ⟨subd9_5_7, List.forall_mem_cons.2 ⟨subd9_5_8, List.forall_mem_cons.2 ⟨subd9_5_9, List.forall_mem_cons.2 ⟨subd9_5_10, List.forall_mem_cons.2 ⟨subd9_5_11, List.forall_mem_cons.2 ⟨subd9_5_12, List.forall_mem_cons.2 ⟨subd9_5_13, List.forall_mem_cons.2 ⟨subd9_5_14, List.forall_mem_cons.2 ⟨subd9_5_15, List.forall_mem_cons.2 ⟨subd9_5_16, List.forall_mem_cons.2 ⟨subd9_5_17, List.forall_mem_cons.2 ⟨subd9_5_18, List.forall_mem_cons.2 ⟨subd9_5_19, List.forall_mem_cons.2 ⟨subd9_5_20, List.forall_mem_cons.2 ⟨subd9_5_21, List.forall_mem_cons.2 ⟨subd9_5_22, List.forall_mem_cons.2 ⟨subd9_5_23, List.forall_mem_cons.2 ⟨subd9_5_24, List.forall_mem_cons.2 ⟨subd9_5_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [-2] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-1, -2] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-1, -1] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-1, 0] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-1, 1] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-1, 2] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [0, -1] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [1, -3] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [1, -2] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [1, -1] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [1, 0] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [1, 1] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [2] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-2] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [-1] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [0, -3] = true := by decide +kernel
theorem subd9_7_3 : subd9_7 [0, -2] = true := by decide +kernel
theorem subd9_7_4 : subd9_7 [0, -1] = true := by decide +kernel
theorem subd9_7_5 : subd9_7 [0, 0] = true := by decide +kernel
theorem subd9_7_6 : subd9_7 [0, 1] = true := by decide +kernel
theorem subd9_7_7 : subd9_7 [0, 2] = true := by decide +kernel
theorem subd9_7_8 : subd9_7 [1] = true := by decide +kernel
theorem subd9_7_9 : subd9_7 [2] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_cons.2 ⟨subd9_7_3, List.forall_mem_cons.2 ⟨subd9_7_4, List.forall_mem_cons.2 ⟨subd9_7_5, List.forall_mem_cons.2 ⟨subd9_7_6, List.forall_mem_cons.2 ⟨subd9_7_7, List.forall_mem_cons.2 ⟨subd9_7_8, List.forall_mem_cons.2 ⟨subd9_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C108
