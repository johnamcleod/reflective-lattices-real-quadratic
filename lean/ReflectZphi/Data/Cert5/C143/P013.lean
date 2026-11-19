import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_2_0 : subd12_2 [-5] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-4, -4] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-4, -3] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-4, -2] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-4, -1] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [-4, 0] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [-4, 1] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [-4, 2] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [-4, 3] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [-3, -5] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [-3, -4] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [-3, -3] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [-3, -2] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [-3, -1] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [-3, 0] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [-3, 1] = true := by decide +kernel
theorem subd12_2_16 : subd12_2 [-3, 2] = true := by decide +kernel
theorem subd12_2_17 : subd12_2 [-3, 3] = true := by decide +kernel
theorem subd12_2_18 : subd12_2 [-3, 4] = true := by decide +kernel
theorem subd12_2_19 : subd12_2 [-2, -5] = true := by decide +kernel
theorem subd12_2_20 : subd12_2 [-2, -4] = true := by decide +kernel
theorem subd12_2_21 : subd12_2 [-2, -3] = true := by decide +kernel
theorem subd12_2_22 : subd12_2 [-2, -2] = true := by decide +kernel
theorem subd12_2_23 : subd12_2 [-2, -1] = true := by decide +kernel
theorem subd12_2_24 : subd12_2 [-2, 0] = true := by decide +kernel
theorem subd12_2_25 : subd12_2 [-2, 1] = true := by decide +kernel
theorem subd12_2_26 : subd12_2 [-2, 2] = true := by decide +kernel
theorem subd12_2_27 : subd12_2 [-2, 3] = true := by decide +kernel
theorem subd12_2_28 : subd12_2 [-2, 4] = true := by decide +kernel
theorem subd12_2_29 : subd12_2 [-1, -6] = true := by decide +kernel
theorem subd12_2_30 : subd12_2 [-1, -5] = true := by decide +kernel
theorem subd12_2_31 : subd12_2 [-1, -4] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_cons.2 ⟨subd12_2_16, List.forall_mem_cons.2 ⟨subd12_2_17, List.forall_mem_cons.2 ⟨subd12_2_18, List.forall_mem_cons.2 ⟨subd12_2_19, List.forall_mem_cons.2 ⟨subd12_2_20, List.forall_mem_cons.2 ⟨subd12_2_21, List.forall_mem_cons.2 ⟨subd12_2_22, List.forall_mem_cons.2 ⟨subd12_2_23, List.forall_mem_cons.2 ⟨subd12_2_24, List.forall_mem_cons.2 ⟨subd12_2_25, List.forall_mem_cons.2 ⟨subd12_2_26, List.forall_mem_cons.2 ⟨subd12_2_27, List.forall_mem_cons.2 ⟨subd12_2_28, List.forall_mem_cons.2 ⟨subd12_2_29, List.forall_mem_cons.2 ⟨subd12_2_30, List.forall_mem_cons.2 ⟨subd12_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_32 : subd12_2 [-1, -3] = true := by decide +kernel
theorem subd12_2_33 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_34 : subd12_2 [-1, -1] = true := by decide +kernel
theorem subd12_2_35 : subd12_2 [-1, 0] = true := by decide +kernel
theorem subd12_2_36 : subd12_2 [-1, 1] = true := by decide +kernel
theorem subd12_2_37 : subd12_2 [-1, 2] = true := by decide +kernel
theorem subd12_2_38 : subd12_2 [-1, 3] = true := by decide +kernel
theorem subd12_2_39 : subd12_2 [-1, 4] = true := by decide +kernel
theorem subd12_2_40 : subd12_2 [0, -6] = true := by decide +kernel
theorem subd12_2_41 : subd12_2 [0, -5] = true := by decide +kernel
theorem subd12_2_42 : subd12_2 [0, -4] = true := by decide +kernel
theorem subd12_2_43 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_44 : subd12_2 [0, -2] = true := by decide +kernel
theorem subd12_2_45 : subd12_2 [0, -1] = true := by decide +kernel
theorem subd12_2_46 : subd12_2 [0, 0] = true := by decide +kernel
theorem subd12_2_47 : subd12_2 [0, 1] = true := by decide +kernel
theorem subd12_2_48 : subd12_2 [0, 2] = true := by decide +kernel
theorem subd12_2_49 : subd12_2 [0, 3] = true := by decide +kernel
theorem subd12_2_50 : subd12_2 [0, 4] = true := by decide +kernel
theorem subd12_2_51 : subd12_2 [0, 5] = true := by decide +kernel
theorem subd12_2_52 : subd12_2 [1, -5] = true := by decide +kernel
theorem subd12_2_53 : subd12_2 [1, -4] = true := by decide +kernel
theorem subd12_2_54 : subd12_2 [1, -3] = true := by decide +kernel
theorem subd12_2_55 : subd12_2 [1, -2] = true := by decide +kernel
theorem subd12_2_56 : subd12_2 [1, -1] = true := by decide +kernel
theorem subd12_2_57 : subd12_2 [1, 0] = true := by decide +kernel
theorem subd12_2_58 : subd12_2 [1, 1] = true := by decide +kernel
theorem subd12_2_59 : subd12_2 [1, 2] = true := by decide +kernel
theorem subd12_2_60 : subd12_2 [1, 3] = true := by decide +kernel
theorem subd12_2_61 : subd12_2 [1, 4] = true := by decide +kernel
theorem subd12_2_62 : subd12_2 [1, 5] = true := by decide +kernel
theorem subd12_2_63 : subd12_2 [2, -5] = true := by decide +kernel
theorem sbd12_2_1 : ∀ q ∈ blkd12_2_1, subd12_2 q = true := by
  unfold blkd12_2_1
  exact List.forall_mem_cons.2 ⟨subd12_2_32, List.forall_mem_cons.2 ⟨subd12_2_33, List.forall_mem_cons.2 ⟨subd12_2_34, List.forall_mem_cons.2 ⟨subd12_2_35, List.forall_mem_cons.2 ⟨subd12_2_36, List.forall_mem_cons.2 ⟨subd12_2_37, List.forall_mem_cons.2 ⟨subd12_2_38, List.forall_mem_cons.2 ⟨subd12_2_39, List.forall_mem_cons.2 ⟨subd12_2_40, List.forall_mem_cons.2 ⟨subd12_2_41, List.forall_mem_cons.2 ⟨subd12_2_42, List.forall_mem_cons.2 ⟨subd12_2_43, List.forall_mem_cons.2 ⟨subd12_2_44, List.forall_mem_cons.2 ⟨subd12_2_45, List.forall_mem_cons.2 ⟨subd12_2_46, List.forall_mem_cons.2 ⟨subd12_2_47, List.forall_mem_cons.2 ⟨subd12_2_48, List.forall_mem_cons.2 ⟨subd12_2_49, List.forall_mem_cons.2 ⟨subd12_2_50, List.forall_mem_cons.2 ⟨subd12_2_51, List.forall_mem_cons.2 ⟨subd12_2_52, List.forall_mem_cons.2 ⟨subd12_2_53, List.forall_mem_cons.2 ⟨subd12_2_54, List.forall_mem_cons.2 ⟨subd12_2_55, List.forall_mem_cons.2 ⟨subd12_2_56, List.forall_mem_cons.2 ⟨subd12_2_57, List.forall_mem_cons.2 ⟨subd12_2_58, List.forall_mem_cons.2 ⟨subd12_2_59, List.forall_mem_cons.2 ⟨subd12_2_60, List.forall_mem_cons.2 ⟨subd12_2_61, List.forall_mem_cons.2 ⟨subd12_2_62, List.forall_mem_cons.2 ⟨subd12_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_2_64 : subd12_2 [2, -4] = true := by decide +kernel
theorem subd12_2_65 : subd12_2 [2, -3] = true := by decide +kernel
theorem subd12_2_66 : subd12_2 [2, -2] = true := by decide +kernel
theorem subd12_2_67 : subd12_2 [2, -1] = true := by decide +kernel
theorem subd12_2_68 : subd12_2 [2, 0] = true := by decide +kernel
theorem subd12_2_69 : subd12_2 [2, 1] = true := by decide +kernel
theorem subd12_2_70 : subd12_2 [2, 2] = true := by decide +kernel
theorem subd12_2_71 : subd12_2 [2, 3] = true := by decide +kernel
theorem subd12_2_72 : subd12_2 [2, 4] = true := by decide +kernel
theorem subd12_2_73 : subd12_2 [3, -5] = true := by decide +kernel
theorem subd12_2_74 : subd12_2 [3, -4] = true := by decide +kernel
theorem subd12_2_75 : subd12_2 [3, -3] = true := by decide +kernel
theorem subd12_2_76 : subd12_2 [3, -2] = true := by decide +kernel
theorem subd12_2_77 : subd12_2 [3, -1] = true := by decide +kernel
theorem subd12_2_78 : subd12_2 [3, 0] = true := by decide +kernel
theorem subd12_2_79 : subd12_2 [3, 1] = true := by decide +kernel
theorem subd12_2_80 : subd12_2 [3, 2] = true := by decide +kernel
theorem subd12_2_81 : subd12_2 [3, 3] = true := by decide +kernel
theorem subd12_2_82 : subd12_2 [3, 4] = true := by decide +kernel
theorem subd12_2_83 : subd12_2 [4, -4] = true := by decide +kernel
theorem subd12_2_84 : subd12_2 [4, -3] = true := by decide +kernel
theorem subd12_2_85 : subd12_2 [4, -2] = true := by decide +kernel
theorem subd12_2_86 : subd12_2 [4, -1] = true := by decide +kernel
theorem subd12_2_87 : subd12_2 [4, 0] = true := by decide +kernel
theorem subd12_2_88 : subd12_2 [4, 1] = true := by decide +kernel
theorem subd12_2_89 : subd12_2 [4, 2] = true := by decide +kernel
theorem subd12_2_90 : subd12_2 [4, 3] = true := by decide +kernel
theorem subd12_2_91 : subd12_2 [5] = true := by decide +kernel
theorem sbd12_2_2 : ∀ q ∈ blkd12_2_2, subd12_2 q = true := by
  unfold blkd12_2_2
  exact List.forall_mem_cons.2 ⟨subd12_2_64, List.forall_mem_cons.2 ⟨subd12_2_65, List.forall_mem_cons.2 ⟨subd12_2_66, List.forall_mem_cons.2 ⟨subd12_2_67, List.forall_mem_cons.2 ⟨subd12_2_68, List.forall_mem_cons.2 ⟨subd12_2_69, List.forall_mem_cons.2 ⟨subd12_2_70, List.forall_mem_cons.2 ⟨subd12_2_71, List.forall_mem_cons.2 ⟨subd12_2_72, List.forall_mem_cons.2 ⟨subd12_2_73, List.forall_mem_cons.2 ⟨subd12_2_74, List.forall_mem_cons.2 ⟨subd12_2_75, List.forall_mem_cons.2 ⟨subd12_2_76, List.forall_mem_cons.2 ⟨subd12_2_77, List.forall_mem_cons.2 ⟨subd12_2_78, List.forall_mem_cons.2 ⟨subd12_2_79, List.forall_mem_cons.2 ⟨subd12_2_80, List.forall_mem_cons.2 ⟨subd12_2_81, List.forall_mem_cons.2 ⟨subd12_2_82, List.forall_mem_cons.2 ⟨subd12_2_83, List.forall_mem_cons.2 ⟨subd12_2_84, List.forall_mem_cons.2 ⟨subd12_2_85, List.forall_mem_cons.2 ⟨subd12_2_86, List.forall_mem_cons.2 ⟨subd12_2_87, List.forall_mem_cons.2 ⟨subd12_2_88, List.forall_mem_cons.2 ⟨subd12_2_89, List.forall_mem_cons.2 ⟨subd12_2_90, List.forall_mem_cons.2 ⟨subd12_2_91, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-3] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-2, -3] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-2, -2] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-2, -1, -8] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-2, -1, -7] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-2, -1, -6] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-2, -1, -5] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [-2, -1, -4] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [-2, -1, -3] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [-2, -1, -2] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [-2, -1, -1] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [-2, -1, 0] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [-2, -1, 1] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [-2, -1, 2] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [-2, -1, 3] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [-2, -1, 4] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [-2, -1, 5] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [-2, -1, 6] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [-2, -1, 7] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [-2, -1, 8] = true := by decide +kernel
theorem subd12_3_20 : subd12_3 [-2, 0, -10] = true := by decide +kernel
theorem subd12_3_21 : subd12_3 [-2, 0, -9] = true := by decide +kernel
theorem subd12_3_22 : subd12_3 [-2, 0, -8] = true := by decide +kernel
theorem subd12_3_23 : subd12_3 [-2, 0, -7] = true := by decide +kernel
theorem subd12_3_24 : subd12_3 [-2, 0, -6] = true := by decide +kernel
theorem subd12_3_25 : subd12_3 [-2, 0, -5] = true := by decide +kernel
theorem subd12_3_26 : subd12_3 [-2, 0, -4] = true := by decide +kernel
theorem subd12_3_27 : subd12_3 [-2, 0, -3] = true := by decide +kernel
theorem subd12_3_28 : subd12_3 [-2, 0, -2] = true := by decide +kernel
theorem subd12_3_29 : subd12_3 [-2, 0, -1] = true := by decide +kernel
theorem subd12_3_30 : subd12_3 [-2, 0, 0] = true := by decide +kernel
theorem subd12_3_31 : subd12_3 [-2, 0, 1] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_cons.2 ⟨subd12_3_20, List.forall_mem_cons.2 ⟨subd12_3_21, List.forall_mem_cons.2 ⟨subd12_3_22, List.forall_mem_cons.2 ⟨subd12_3_23, List.forall_mem_cons.2 ⟨subd12_3_24, List.forall_mem_cons.2 ⟨subd12_3_25, List.forall_mem_cons.2 ⟨subd12_3_26, List.forall_mem_cons.2 ⟨subd12_3_27, List.forall_mem_cons.2 ⟨subd12_3_28, List.forall_mem_cons.2 ⟨subd12_3_29, List.forall_mem_cons.2 ⟨subd12_3_30, List.forall_mem_cons.2 ⟨subd12_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_32 : subd12_3 [-2, 0, 2] = true := by decide +kernel
theorem subd12_3_33 : subd12_3 [-2, 0, 3] = true := by decide +kernel
theorem subd12_3_34 : subd12_3 [-2, 0, 4] = true := by decide +kernel
theorem subd12_3_35 : subd12_3 [-2, 0, 5] = true := by decide +kernel
theorem subd12_3_36 : subd12_3 [-2, 0, 6] = true := by decide +kernel
theorem subd12_3_37 : subd12_3 [-2, 0, 7] = true := by decide +kernel
theorem subd12_3_38 : subd12_3 [-2, 0, 8] = true := by decide +kernel
theorem subd12_3_39 : subd12_3 [-2, 0, 9] = true := by decide +kernel
theorem subd12_3_40 : subd12_3 [-2, 1, -9] = true := by decide +kernel
theorem subd12_3_41 : subd12_3 [-2, 1, -8] = true := by decide +kernel
theorem subd12_3_42 : subd12_3 [-2, 1, -7] = true := by decide +kernel
theorem subd12_3_43 : subd12_3 [-2, 1, -6] = true := by decide +kernel
theorem subd12_3_44 : subd12_3 [-2, 1, -5] = true := by decide +kernel
theorem subd12_3_45 : subd12_3 [-2, 1, -4] = true := by decide +kernel
theorem subd12_3_46 : subd12_3 [-2, 1, -3] = true := by decide +kernel
theorem subd12_3_47 : subd12_3 [-2, 1, -2] = true := by decide +kernel
theorem subd12_3_48 : subd12_3 [-2, 1, -1] = true := by decide +kernel
theorem subd12_3_49 : subd12_3 [-2, 1, 0] = true := by decide +kernel
theorem subd12_3_50 : subd12_3 [-2, 1, 1] = true := by decide +kernel
theorem subd12_3_51 : subd12_3 [-2, 1, 2] = true := by decide +kernel
theorem subd12_3_52 : subd12_3 [-2, 1, 3] = true := by decide +kernel
theorem subd12_3_53 : subd12_3 [-2, 1, 4] = true := by decide +kernel
theorem subd12_3_54 : subd12_3 [-2, 1, 5] = true := by decide +kernel
theorem subd12_3_55 : subd12_3 [-2, 1, 6] = true := by decide +kernel
theorem subd12_3_56 : subd12_3 [-2, 1, 7] = true := by decide +kernel
theorem subd12_3_57 : subd12_3 [-2, 1, 8] = true := by decide +kernel
theorem subd12_3_58 : subd12_3 [-2, 2] = true := by decide +kernel
theorem subd12_3_59 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_60 : subd12_3 [-1, -2, -8] = true := by decide +kernel
theorem subd12_3_61 : subd12_3 [-1, -2, -7] = true := by decide +kernel
theorem subd12_3_62 : subd12_3 [-1, -2, -6] = true := by decide +kernel
theorem subd12_3_63 : subd12_3 [-1, -2, -5] = true := by decide +kernel
theorem sbd12_3_1 : ∀ q ∈ blkd12_3_1, subd12_3 q = true := by
  unfold blkd12_3_1
  exact List.forall_mem_cons.2 ⟨subd12_3_32, List.forall_mem_cons.2 ⟨subd12_3_33, List.forall_mem_cons.2 ⟨subd12_3_34, List.forall_mem_cons.2 ⟨subd12_3_35, List.forall_mem_cons.2 ⟨subd12_3_36, List.forall_mem_cons.2 ⟨subd12_3_37, List.forall_mem_cons.2 ⟨subd12_3_38, List.forall_mem_cons.2 ⟨subd12_3_39, List.forall_mem_cons.2 ⟨subd12_3_40, List.forall_mem_cons.2 ⟨subd12_3_41, List.forall_mem_cons.2 ⟨subd12_3_42, List.forall_mem_cons.2 ⟨subd12_3_43, List.forall_mem_cons.2 ⟨subd12_3_44, List.forall_mem_cons.2 ⟨subd12_3_45, List.forall_mem_cons.2 ⟨subd12_3_46, List.forall_mem_cons.2 ⟨subd12_3_47, List.forall_mem_cons.2 ⟨subd12_3_48, List.forall_mem_cons.2 ⟨subd12_3_49, List.forall_mem_cons.2 ⟨subd12_3_50, List.forall_mem_cons.2 ⟨subd12_3_51, List.forall_mem_cons.2 ⟨subd12_3_52, List.forall_mem_cons.2 ⟨subd12_3_53, List.forall_mem_cons.2 ⟨subd12_3_54, List.forall_mem_cons.2 ⟨subd12_3_55, List.forall_mem_cons.2 ⟨subd12_3_56, List.forall_mem_cons.2 ⟨subd12_3_57, List.forall_mem_cons.2 ⟨subd12_3_58, List.forall_mem_cons.2 ⟨subd12_3_59, List.forall_mem_cons.2 ⟨subd12_3_60, List.forall_mem_cons.2 ⟨subd12_3_61, List.forall_mem_cons.2 ⟨subd12_3_62, List.forall_mem_cons.2 ⟨subd12_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_3_64 : subd12_3 [-1, -2, -4] = true := by decide +kernel
theorem subd12_3_65 : subd12_3 [-1, -2, -3] = true := by decide +kernel
theorem subd12_3_66 : subd12_3 [-1, -2, -2] = true := by decide +kernel
theorem subd12_3_67 : subd12_3 [-1, -2, -1] = true := by decide +kernel
theorem subd12_3_68 : subd12_3 [-1, -2, 0] = true := by decide +kernel
theorem subd12_3_69 : subd12_3 [-1, -2, 1] = true := by decide +kernel
theorem subd12_3_70 : subd12_3 [-1, -2, 2] = true := by decide +kernel
theorem subd12_3_71 : subd12_3 [-1, -2, 3] = true := by decide +kernel
theorem subd12_3_72 : subd12_3 [-1, -2, 4] = true := by decide +kernel
theorem subd12_3_73 : subd12_3 [-1, -2, 5] = true := by decide +kernel
theorem subd12_3_74 : subd12_3 [-1, -2, 6] = true := by decide +kernel
theorem subd12_3_75 : subd12_3 [-1, -2, 7] = true := by decide +kernel
theorem subd12_3_76 : subd12_3 [-1, -2, 8] = true := by decide +kernel
theorem subd12_3_77 : subd12_3 [-1, -1, -11] = true := by decide +kernel
theorem subd12_3_78 : subd12_3 [-1, -1, -10] = true := by decide +kernel
theorem subd12_3_79 : subd12_3 [-1, -1, -9] = true := by decide +kernel
theorem subd12_3_80 : subd12_3 [-1, -1, -8] = true := by decide +kernel
theorem subd12_3_81 : subd12_3 [-1, -1, -7] = true := by decide +kernel
theorem subd12_3_82 : subd12_3 [-1, -1, -6] = true := by decide +kernel
theorem subd12_3_83 : subd12_3 [-1, -1, -5] = true := by decide +kernel
theorem subd12_3_84 : subd12_3 [-1, -1, -4] = true := by decide +kernel
theorem subd12_3_85 : subd12_3 [-1, -1, -3] = true := by decide +kernel
theorem subd12_3_86 : subd12_3 [-1, -1, -2] = true := by decide +kernel
theorem subd12_3_87 : subd12_3 [-1, -1, -1] = true := by decide +kernel
theorem subd12_3_88 : subd12_3 [-1, -1, 0] = true := by decide +kernel
theorem subd12_3_89 : subd12_3 [-1, -1, 1] = true := by decide +kernel
theorem subd12_3_90 : subd12_3 [-1, -1, 2] = true := by decide +kernel
theorem subd12_3_91 : subd12_3 [-1, -1, 3] = true := by decide +kernel
theorem subd12_3_92 : subd12_3 [-1, -1, 4] = true := by decide +kernel
theorem subd12_3_93 : subd12_3 [-1, -1, 5] = true := by decide +kernel
theorem subd12_3_94 : subd12_3 [-1, -1, 6] = true := by decide +kernel
theorem subd12_3_95 : subd12_3 [-1, -1, 7] = true := by decide +kernel
theorem sbd12_3_2 : ∀ q ∈ blkd12_3_2, subd12_3 q = true := by
  unfold blkd12_3_2
  exact List.forall_mem_cons.2 ⟨subd12_3_64, List.forall_mem_cons.2 ⟨subd12_3_65, List.forall_mem_cons.2 ⟨subd12_3_66, List.forall_mem_cons.2 ⟨subd12_3_67, List.forall_mem_cons.2 ⟨subd12_3_68, List.forall_mem_cons.2 ⟨subd12_3_69, List.forall_mem_cons.2 ⟨subd12_3_70, List.forall_mem_cons.2 ⟨subd12_3_71, List.forall_mem_cons.2 ⟨subd12_3_72, List.forall_mem_cons.2 ⟨subd12_3_73, List.forall_mem_cons.2 ⟨subd12_3_74, List.forall_mem_cons.2 ⟨subd12_3_75, List.forall_mem_cons.2 ⟨subd12_3_76, List.forall_mem_cons.2 ⟨subd12_3_77, List.forall_mem_cons.2 ⟨subd12_3_78, List.forall_mem_cons.2 ⟨subd12_3_79, List.forall_mem_cons.2 ⟨subd12_3_80, List.forall_mem_cons.2 ⟨subd12_3_81, List.forall_mem_cons.2 ⟨subd12_3_82, List.forall_mem_cons.2 ⟨subd12_3_83, List.forall_mem_cons.2 ⟨subd12_3_84, List.forall_mem_cons.2 ⟨subd12_3_85, List.forall_mem_cons.2 ⟨subd12_3_86, List.forall_mem_cons.2 ⟨subd12_3_87, List.forall_mem_cons.2 ⟨subd12_3_88, List.forall_mem_cons.2 ⟨subd12_3_89, List.forall_mem_cons.2 ⟨subd12_3_90, List.forall_mem_cons.2 ⟨subd12_3_91, List.forall_mem_cons.2 ⟨subd12_3_92, List.forall_mem_cons.2 ⟨subd12_3_93, List.forall_mem_cons.2 ⟨subd12_3_94, List.forall_mem_cons.2 ⟨subd12_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
