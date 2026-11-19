import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_32 : subd14_0 [1, -3] = true := by decide +kernel
theorem subd14_0_33 : subd14_0 [1, -2] = true := by decide +kernel
theorem subd14_0_34 : subd14_0 [1, -1] = true := by decide +kernel
theorem subd14_0_35 : subd14_0 [1, 0] = true := by decide +kernel
theorem subd14_0_36 : subd14_0 [1, 1] = true := by decide +kernel
theorem subd14_0_37 : subd14_0 [1, 2] = true := by decide +kernel
theorem subd14_0_38 : subd14_0 [1, 3] = true := by decide +kernel
theorem subd14_0_39 : subd14_0 [1, 4] = true := by decide +kernel
theorem subd14_0_40 : subd14_0 [2, -4] = true := by decide +kernel
theorem subd14_0_41 : subd14_0 [2, -3] = true := by decide +kernel
theorem subd14_0_42 : subd14_0 [2, -2] = true := by decide +kernel
theorem subd14_0_43 : subd14_0 [2, -1] = true := by decide +kernel
theorem subd14_0_44 : subd14_0 [2, 0] = true := by decide +kernel
theorem subd14_0_45 : subd14_0 [2, 1] = true := by decide +kernel
theorem subd14_0_46 : subd14_0 [2, 2] = true := by decide +kernel
theorem subd14_0_47 : subd14_0 [2, 3] = true := by decide +kernel
theorem subd14_0_48 : subd14_0 [3] = true := by decide +kernel
theorem subd14_0_49 : subd14_0 [4] = true := by decide +kernel
theorem sbd14_0_1 : ∀ q ∈ blkd14_0_1, subd14_0 q = true := by
  unfold blkd14_0_1
  exact List.forall_mem_cons.2 ⟨subd14_0_32, List.forall_mem_cons.2 ⟨subd14_0_33, List.forall_mem_cons.2 ⟨subd14_0_34, List.forall_mem_cons.2 ⟨subd14_0_35, List.forall_mem_cons.2 ⟨subd14_0_36, List.forall_mem_cons.2 ⟨subd14_0_37, List.forall_mem_cons.2 ⟨subd14_0_38, List.forall_mem_cons.2 ⟨subd14_0_39, List.forall_mem_cons.2 ⟨subd14_0_40, List.forall_mem_cons.2 ⟨subd14_0_41, List.forall_mem_cons.2 ⟨subd14_0_42, List.forall_mem_cons.2 ⟨subd14_0_43, List.forall_mem_cons.2 ⟨subd14_0_44, List.forall_mem_cons.2 ⟨subd14_0_45, List.forall_mem_cons.2 ⟨subd14_0_46, List.forall_mem_cons.2 ⟨subd14_0_47, List.forall_mem_cons.2 ⟨subd14_0_48, List.forall_mem_cons.2 ⟨subd14_0_49, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-3] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-2, -5] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-2, -4] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-2, -3] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-2, -2] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-2, -1] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-2, 0] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-2, 1] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-2, 2] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-1, -4] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-1, -3] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [-1, -1] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [-1, 0] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [-1, 1] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [-1, 2] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [0, -4] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [0, -1] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [0, 3] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [1, -3] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [1, -2] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [1, -1] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [1, 0] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [1, 1] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [1, 2] = true := by decide +kernel
theorem subd14_1_30 : subd14_1 [1, 3] = true := by decide +kernel
theorem subd14_1_31 : subd14_1 [2, -3] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_cons.2 ⟨subd14_1_30, List.forall_mem_cons.2 ⟨subd14_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_32 : subd14_1 [2, -2] = true := by decide +kernel
theorem subd14_1_33 : subd14_1 [2, -1] = true := by decide +kernel
theorem subd14_1_34 : subd14_1 [2, 0] = true := by decide +kernel
theorem subd14_1_35 : subd14_1 [2, 1] = true := by decide +kernel
theorem subd14_1_36 : subd14_1 [2, 2] = true := by decide +kernel
theorem subd14_1_37 : subd14_1 [2, 3] = true := by decide +kernel
theorem subd14_1_38 : subd14_1 [2, 4] = true := by decide +kernel
theorem subd14_1_39 : subd14_1 [3] = true := by decide +kernel
theorem sbd14_1_1 : ∀ q ∈ blkd14_1_1, subd14_1 q = true := by
  unfold blkd14_1_1
  exact List.forall_mem_cons.2 ⟨subd14_1_32, List.forall_mem_cons.2 ⟨subd14_1_33, List.forall_mem_cons.2 ⟨subd14_1_34, List.forall_mem_cons.2 ⟨subd14_1_35, List.forall_mem_cons.2 ⟨subd14_1_36, List.forall_mem_cons.2 ⟨subd14_1_37, List.forall_mem_cons.2 ⟨subd14_1_38, List.forall_mem_cons.2 ⟨subd14_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-5, -1] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-5, 0] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [-5, 1] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [-5, 2] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [-5, 3] = true := by decide +kernel
theorem subd14_2_5 : subd14_2 [-5, 4] = true := by decide +kernel
theorem subd14_2_6 : subd14_2 [-4, -3] = true := by decide +kernel
theorem subd14_2_7 : subd14_2 [-4, -2] = true := by decide +kernel
theorem subd14_2_8 : subd14_2 [-4, -1] = true := by decide +kernel
theorem subd14_2_9 : subd14_2 [-4, 0] = true := by decide +kernel
theorem subd14_2_10 : subd14_2 [-4, 1] = true := by decide +kernel
theorem subd14_2_11 : subd14_2 [-4, 2] = true := by decide +kernel
theorem subd14_2_12 : subd14_2 [-4, 3] = true := by decide +kernel
theorem subd14_2_13 : subd14_2 [-4, 4] = true := by decide +kernel
theorem subd14_2_14 : subd14_2 [-4, 5] = true := by decide +kernel
theorem subd14_2_15 : subd14_2 [-3, -5] = true := by decide +kernel
theorem subd14_2_16 : subd14_2 [-3, -4] = true := by decide +kernel
theorem subd14_2_17 : subd14_2 [-3, -3] = true := by decide +kernel
theorem subd14_2_18 : subd14_2 [-3, -2] = true := by decide +kernel
theorem subd14_2_19 : subd14_2 [-3, -1, -8] = true := by decide +kernel
theorem subd14_2_20 : subd14_2 [-3, -1, -7] = true := by decide +kernel
theorem subd14_2_21 : subd14_2 [-3, -1, -6] = true := by decide +kernel
theorem subd14_2_22 : subd14_2 [-3, -1, -5] = true := by decide +kernel
theorem subd14_2_23 : subd14_2 [-3, -1, -4] = true := by decide +kernel
theorem subd14_2_24 : subd14_2 [-3, -1, -3] = true := by decide +kernel
theorem subd14_2_25 : subd14_2 [-3, -1, -2] = true := by decide +kernel
theorem subd14_2_26 : subd14_2 [-3, -1, -1] = true := by decide +kernel
theorem subd14_2_27 : subd14_2 [-3, -1, 0] = true := by decide +kernel
theorem subd14_2_28 : subd14_2 [-3, -1, 1] = true := by decide +kernel
theorem subd14_2_29 : subd14_2 [-3, -1, 2] = true := by decide +kernel
theorem subd14_2_30 : subd14_2 [-3, -1, 3] = true := by decide +kernel
theorem subd14_2_31 : subd14_2 [-3, -1, 4] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_cons.2 ⟨subd14_2_5, List.forall_mem_cons.2 ⟨subd14_2_6, List.forall_mem_cons.2 ⟨subd14_2_7, List.forall_mem_cons.2 ⟨subd14_2_8, List.forall_mem_cons.2 ⟨subd14_2_9, List.forall_mem_cons.2 ⟨subd14_2_10, List.forall_mem_cons.2 ⟨subd14_2_11, List.forall_mem_cons.2 ⟨subd14_2_12, List.forall_mem_cons.2 ⟨subd14_2_13, List.forall_mem_cons.2 ⟨subd14_2_14, List.forall_mem_cons.2 ⟨subd14_2_15, List.forall_mem_cons.2 ⟨subd14_2_16, List.forall_mem_cons.2 ⟨subd14_2_17, List.forall_mem_cons.2 ⟨subd14_2_18, List.forall_mem_cons.2 ⟨subd14_2_19, List.forall_mem_cons.2 ⟨subd14_2_20, List.forall_mem_cons.2 ⟨subd14_2_21, List.forall_mem_cons.2 ⟨subd14_2_22, List.forall_mem_cons.2 ⟨subd14_2_23, List.forall_mem_cons.2 ⟨subd14_2_24, List.forall_mem_cons.2 ⟨subd14_2_25, List.forall_mem_cons.2 ⟨subd14_2_26, List.forall_mem_cons.2 ⟨subd14_2_27, List.forall_mem_cons.2 ⟨subd14_2_28, List.forall_mem_cons.2 ⟨subd14_2_29, List.forall_mem_cons.2 ⟨subd14_2_30, List.forall_mem_cons.2 ⟨subd14_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_32 : subd14_2 [-3, -1, 5] = true := by decide +kernel
theorem subd14_2_33 : subd14_2 [-3, -1, 6] = true := by decide +kernel
theorem subd14_2_34 : subd14_2 [-3, 0, -9] = true := by decide +kernel
theorem subd14_2_35 : subd14_2 [-3, 0, -8] = true := by decide +kernel
theorem subd14_2_36 : subd14_2 [-3, 0, -7] = true := by decide +kernel
theorem subd14_2_37 : subd14_2 [-3, 0, -6] = true := by decide +kernel
theorem subd14_2_38 : subd14_2 [-3, 0, -5] = true := by decide +kernel
theorem subd14_2_39 : subd14_2 [-3, 0, -4] = true := by decide +kernel
theorem subd14_2_40 : subd14_2 [-3, 0, -3] = true := by decide +kernel
theorem subd14_2_41 : subd14_2 [-3, 0, -2] = true := by decide +kernel
theorem subd14_2_42 : subd14_2 [-3, 0, -1] = true := by decide +kernel
theorem subd14_2_43 : subd14_2 [-3, 0, 0] = true := by decide +kernel
theorem subd14_2_44 : subd14_2 [-3, 0, 1] = true := by decide +kernel
theorem subd14_2_45 : subd14_2 [-3, 0, 2] = true := by decide +kernel
theorem subd14_2_46 : subd14_2 [-3, 0, 3] = true := by decide +kernel
theorem subd14_2_47 : subd14_2 [-3, 0, 4] = true := by decide +kernel
theorem subd14_2_48 : subd14_2 [-3, 0, 5] = true := by decide +kernel
theorem subd14_2_49 : subd14_2 [-3, 0, 6] = true := by decide +kernel
theorem subd14_2_50 : subd14_2 [-3, 1, -9] = true := by decide +kernel
theorem subd14_2_51 : subd14_2 [-3, 1, -8] = true := by decide +kernel
theorem subd14_2_52 : subd14_2 [-3, 1, -7] = true := by decide +kernel
theorem subd14_2_53 : subd14_2 [-3, 1, -6] = true := by decide +kernel
theorem subd14_2_54 : subd14_2 [-3, 1, -5] = true := by decide +kernel
theorem subd14_2_55 : subd14_2 [-3, 1, -4] = true := by decide +kernel
theorem subd14_2_56 : subd14_2 [-3, 1, -3] = true := by decide +kernel
theorem subd14_2_57 : subd14_2 [-3, 1, -2] = true := by decide +kernel
theorem subd14_2_58 : subd14_2 [-3, 1, -1] = true := by decide +kernel
theorem subd14_2_59 : subd14_2 [-3, 1, 0] = true := by decide +kernel
theorem subd14_2_60 : subd14_2 [-3, 1, 1] = true := by decide +kernel
theorem subd14_2_61 : subd14_2 [-3, 1, 2] = true := by decide +kernel
theorem subd14_2_62 : subd14_2 [-3, 1, 3] = true := by decide +kernel
theorem subd14_2_63 : subd14_2 [-3, 1, 4] = true := by decide +kernel
theorem sbd14_2_1 : ∀ q ∈ blkd14_2_1, subd14_2 q = true := by
  unfold blkd14_2_1
  exact List.forall_mem_cons.2 ⟨subd14_2_32, List.forall_mem_cons.2 ⟨subd14_2_33, List.forall_mem_cons.2 ⟨subd14_2_34, List.forall_mem_cons.2 ⟨subd14_2_35, List.forall_mem_cons.2 ⟨subd14_2_36, List.forall_mem_cons.2 ⟨subd14_2_37, List.forall_mem_cons.2 ⟨subd14_2_38, List.forall_mem_cons.2 ⟨subd14_2_39, List.forall_mem_cons.2 ⟨subd14_2_40, List.forall_mem_cons.2 ⟨subd14_2_41, List.forall_mem_cons.2 ⟨subd14_2_42, List.forall_mem_cons.2 ⟨subd14_2_43, List.forall_mem_cons.2 ⟨subd14_2_44, List.forall_mem_cons.2 ⟨subd14_2_45, List.forall_mem_cons.2 ⟨subd14_2_46, List.forall_mem_cons.2 ⟨subd14_2_47, List.forall_mem_cons.2 ⟨subd14_2_48, List.forall_mem_cons.2 ⟨subd14_2_49, List.forall_mem_cons.2 ⟨subd14_2_50, List.forall_mem_cons.2 ⟨subd14_2_51, List.forall_mem_cons.2 ⟨subd14_2_52, List.forall_mem_cons.2 ⟨subd14_2_53, List.forall_mem_cons.2 ⟨subd14_2_54, List.forall_mem_cons.2 ⟨subd14_2_55, List.forall_mem_cons.2 ⟨subd14_2_56, List.forall_mem_cons.2 ⟨subd14_2_57, List.forall_mem_cons.2 ⟨subd14_2_58, List.forall_mem_cons.2 ⟨subd14_2_59, List.forall_mem_cons.2 ⟨subd14_2_60, List.forall_mem_cons.2 ⟨subd14_2_61, List.forall_mem_cons.2 ⟨subd14_2_62, List.forall_mem_cons.2 ⟨subd14_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_64 : subd14_2 [-3, 1, 5] = true := by decide +kernel
theorem subd14_2_65 : subd14_2 [-3, 1, 6] = true := by decide +kernel
theorem subd14_2_66 : subd14_2 [-3, 2, -9] = true := by decide +kernel
theorem subd14_2_67 : subd14_2 [-3, 2, -8] = true := by decide +kernel
theorem subd14_2_68 : subd14_2 [-3, 2, -7] = true := by decide +kernel
theorem subd14_2_69 : subd14_2 [-3, 2, -6] = true := by decide +kernel
theorem subd14_2_70 : subd14_2 [-3, 2, -5] = true := by decide +kernel
theorem subd14_2_71 : subd14_2 [-3, 2, -4] = true := by decide +kernel
theorem subd14_2_72 : subd14_2 [-3, 2, -3] = true := by decide +kernel
theorem subd14_2_73 : subd14_2 [-3, 2, -2] = true := by decide +kernel
theorem subd14_2_74 : subd14_2 [-3, 2, -1] = true := by decide +kernel
theorem subd14_2_75 : subd14_2 [-3, 2, 0] = true := by decide +kernel
theorem subd14_2_76 : subd14_2 [-3, 2, 1] = true := by decide +kernel
theorem subd14_2_77 : subd14_2 [-3, 2, 2] = true := by decide +kernel
theorem subd14_2_78 : subd14_2 [-3, 2, 3] = true := by decide +kernel
theorem subd14_2_79 : subd14_2 [-3, 2, 4] = true := by decide +kernel
theorem subd14_2_80 : subd14_2 [-3, 2, 5] = true := by decide +kernel
theorem subd14_2_81 : subd14_2 [-3, 2, 6] = true := by decide +kernel
theorem subd14_2_82 : subd14_2 [-3, 3, -8] = true := by decide +kernel
theorem subd14_2_83 : subd14_2 [-3, 3, -7] = true := by decide +kernel
theorem subd14_2_84 : subd14_2 [-3, 3, -6] = true := by decide +kernel
theorem subd14_2_85 : subd14_2 [-3, 3, -5] = true := by decide +kernel
theorem subd14_2_86 : subd14_2 [-3, 3, -4] = true := by decide +kernel
theorem subd14_2_87 : subd14_2 [-3, 3, -3] = true := by decide +kernel
theorem subd14_2_88 : subd14_2 [-3, 3, -2] = true := by decide +kernel
theorem subd14_2_89 : subd14_2 [-3, 3, -1] = true := by decide +kernel
theorem subd14_2_90 : subd14_2 [-3, 3, 0] = true := by decide +kernel
theorem subd14_2_91 : subd14_2 [-3, 3, 1] = true := by decide +kernel
theorem subd14_2_92 : subd14_2 [-3, 3, 2] = true := by decide +kernel
theorem subd14_2_93 : subd14_2 [-3, 3, 3] = true := by decide +kernel
theorem subd14_2_94 : subd14_2 [-3, 3, 4] = true := by decide +kernel
theorem subd14_2_95 : subd14_2 [-3, 3, 5] = true := by decide +kernel
theorem sbd14_2_2 : ∀ q ∈ blkd14_2_2, subd14_2 q = true := by
  unfold blkd14_2_2
  exact List.forall_mem_cons.2 ⟨subd14_2_64, List.forall_mem_cons.2 ⟨subd14_2_65, List.forall_mem_cons.2 ⟨subd14_2_66, List.forall_mem_cons.2 ⟨subd14_2_67, List.forall_mem_cons.2 ⟨subd14_2_68, List.forall_mem_cons.2 ⟨subd14_2_69, List.forall_mem_cons.2 ⟨subd14_2_70, List.forall_mem_cons.2 ⟨subd14_2_71, List.forall_mem_cons.2 ⟨subd14_2_72, List.forall_mem_cons.2 ⟨subd14_2_73, List.forall_mem_cons.2 ⟨subd14_2_74, List.forall_mem_cons.2 ⟨subd14_2_75, List.forall_mem_cons.2 ⟨subd14_2_76, List.forall_mem_cons.2 ⟨subd14_2_77, List.forall_mem_cons.2 ⟨subd14_2_78, List.forall_mem_cons.2 ⟨subd14_2_79, List.forall_mem_cons.2 ⟨subd14_2_80, List.forall_mem_cons.2 ⟨subd14_2_81, List.forall_mem_cons.2 ⟨subd14_2_82, List.forall_mem_cons.2 ⟨subd14_2_83, List.forall_mem_cons.2 ⟨subd14_2_84, List.forall_mem_cons.2 ⟨subd14_2_85, List.forall_mem_cons.2 ⟨subd14_2_86, List.forall_mem_cons.2 ⟨subd14_2_87, List.forall_mem_cons.2 ⟨subd14_2_88, List.forall_mem_cons.2 ⟨subd14_2_89, List.forall_mem_cons.2 ⟨subd14_2_90, List.forall_mem_cons.2 ⟨subd14_2_91, List.forall_mem_cons.2 ⟨subd14_2_92, List.forall_mem_cons.2 ⟨subd14_2_93, List.forall_mem_cons.2 ⟨subd14_2_94, List.forall_mem_cons.2 ⟨subd14_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_96 : subd14_2 [-3, 3, 6] = true := by decide +kernel
theorem subd14_2_97 : subd14_2 [-3, 4] = true := by decide +kernel
theorem subd14_2_98 : subd14_2 [-3, 5] = true := by decide +kernel
theorem subd14_2_99 : subd14_2 [-3, 6] = true := by decide +kernel
theorem subd14_2_100 : subd14_2 [-2, -6] = true := by decide +kernel
theorem subd14_2_101 : subd14_2 [-2, -5] = true := by decide +kernel
theorem subd14_2_102 : subd14_2 [-2, -4] = true := by decide +kernel
theorem subd14_2_103 : subd14_2 [-2, -3, -8] = true := by decide +kernel
theorem subd14_2_104 : subd14_2 [-2, -3, -7] = true := by decide +kernel
theorem subd14_2_105 : subd14_2 [-2, -3, -6] = true := by decide +kernel
theorem subd14_2_106 : subd14_2 [-2, -3, -5] = true := by decide +kernel
theorem subd14_2_107 : subd14_2 [-2, -3, -4] = true := by decide +kernel
theorem subd14_2_108 : subd14_2 [-2, -3, -3] = true := by decide +kernel
theorem subd14_2_109 : subd14_2 [-2, -3, -2] = true := by decide +kernel
theorem subd14_2_110 : subd14_2 [-2, -3, -1] = true := by decide +kernel
theorem subd14_2_111 : subd14_2 [-2, -3, 0] = true := by decide +kernel
theorem subd14_2_112 : subd14_2 [-2, -3, 1] = true := by decide +kernel
theorem subd14_2_113 : subd14_2 [-2, -3, 2] = true := by decide +kernel
theorem subd14_2_114 : subd14_2 [-2, -3, 3] = true := by decide +kernel
theorem subd14_2_115 : subd14_2 [-2, -3, 4] = true := by decide +kernel
theorem subd14_2_116 : subd14_2 [-2, -3, 5] = true := by decide +kernel
theorem subd14_2_117 : subd14_2 [-2, -2, -9] = true := by decide +kernel
theorem subd14_2_118 : subd14_2 [-2, -2, -8] = true := by decide +kernel
theorem subd14_2_119 : subd14_2 [-2, -2, -7] = true := by decide +kernel
theorem subd14_2_120 : subd14_2 [-2, -2, -6] = true := by decide +kernel
theorem subd14_2_121 : subd14_2 [-2, -2, -5] = true := by decide +kernel
theorem subd14_2_122 : subd14_2 [-2, -2, -4] = true := by decide +kernel
theorem subd14_2_123 : subd14_2 [-2, -2, -3] = true := by decide +kernel
theorem subd14_2_124 : subd14_2 [-2, -2, -2] = true := by decide +kernel
theorem subd14_2_125 : subd14_2 [-2, -2, -1] = true := by decide +kernel
theorem subd14_2_126 : subd14_2 [-2, -2, 0] = true := by decide +kernel
theorem subd14_2_127 : subd14_2 [-2, -2, 1] = true := by decide +kernel
theorem sbd14_2_3 : ∀ q ∈ blkd14_2_3, subd14_2 q = true := by
  unfold blkd14_2_3
  exact List.forall_mem_cons.2 ⟨subd14_2_96, List.forall_mem_cons.2 ⟨subd14_2_97, List.forall_mem_cons.2 ⟨subd14_2_98, List.forall_mem_cons.2 ⟨subd14_2_99, List.forall_mem_cons.2 ⟨subd14_2_100, List.forall_mem_cons.2 ⟨subd14_2_101, List.forall_mem_cons.2 ⟨subd14_2_102, List.forall_mem_cons.2 ⟨subd14_2_103, List.forall_mem_cons.2 ⟨subd14_2_104, List.forall_mem_cons.2 ⟨subd14_2_105, List.forall_mem_cons.2 ⟨subd14_2_106, List.forall_mem_cons.2 ⟨subd14_2_107, List.forall_mem_cons.2 ⟨subd14_2_108, List.forall_mem_cons.2 ⟨subd14_2_109, List.forall_mem_cons.2 ⟨subd14_2_110, List.forall_mem_cons.2 ⟨subd14_2_111, List.forall_mem_cons.2 ⟨subd14_2_112, List.forall_mem_cons.2 ⟨subd14_2_113, List.forall_mem_cons.2 ⟨subd14_2_114, List.forall_mem_cons.2 ⟨subd14_2_115, List.forall_mem_cons.2 ⟨subd14_2_116, List.forall_mem_cons.2 ⟨subd14_2_117, List.forall_mem_cons.2 ⟨subd14_2_118, List.forall_mem_cons.2 ⟨subd14_2_119, List.forall_mem_cons.2 ⟨subd14_2_120, List.forall_mem_cons.2 ⟨subd14_2_121, List.forall_mem_cons.2 ⟨subd14_2_122, List.forall_mem_cons.2 ⟨subd14_2_123, List.forall_mem_cons.2 ⟨subd14_2_124, List.forall_mem_cons.2 ⟨subd14_2_125, List.forall_mem_cons.2 ⟨subd14_2_126, List.forall_mem_cons.2 ⟨subd14_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_128 : subd14_2 [-2, -2, 2] = true := by decide +kernel
theorem subd14_2_129 : subd14_2 [-2, -2, 3] = true := by decide +kernel
theorem subd14_2_130 : subd14_2 [-2, -2, 4] = true := by decide +kernel
theorem subd14_2_131 : subd14_2 [-2, -2, 5] = true := by decide +kernel
theorem subd14_2_132 : subd14_2 [-2, -2, 6] = true := by decide +kernel
theorem subd14_2_133 : subd14_2 [-2, -1, -9] = true := by decide +kernel
theorem subd14_2_134 : subd14_2 [-2, -1, -8] = true := by decide +kernel
theorem subd14_2_135 : subd14_2 [-2, -1, -7] = true := by decide +kernel
theorem subd14_2_136 : subd14_2 [-2, -1, -6] = true := by decide +kernel
theorem subd14_2_137 : subd14_2 [-2, -1, -5] = true := by decide +kernel
theorem subd14_2_138 : subd14_2 [-2, -1, -4] = true := by decide +kernel
theorem subd14_2_139 : subd14_2 [-2, -1, -3] = true := by decide +kernel
theorem subd14_2_140 : subd14_2 [-2, -1, -2] = true := by decide +kernel
theorem subd14_2_141 : subd14_2 [-2, -1, -1] = true := by decide +kernel
theorem subd14_2_142 : subd14_2 [-2, -1, 0] = true := by decide +kernel
theorem subd14_2_143 : subd14_2 [-2, -1, 1] = true := by decide +kernel
theorem subd14_2_144 : subd14_2 [-2, -1, 2] = true := by decide +kernel
theorem subd14_2_145 : subd14_2 [-2, -1, 3] = true := by decide +kernel
theorem subd14_2_146 : subd14_2 [-2, -1, 4] = true := by decide +kernel
theorem subd14_2_147 : subd14_2 [-2, -1, 5] = true := by decide +kernel
theorem subd14_2_148 : subd14_2 [-2, -1, 6] = true := by decide +kernel
theorem subd14_2_149 : subd14_2 [-2, -1, 7] = true := by decide +kernel
theorem subd14_2_150 : subd14_2 [-2, 0, -9] = true := by decide +kernel
theorem subd14_2_151 : subd14_2 [-2, 0, -8] = true := by decide +kernel
theorem subd14_2_152 : subd14_2 [-2, 0, -7] = true := by decide +kernel
theorem subd14_2_153 : subd14_2 [-2, 0, -6] = true := by decide +kernel
theorem subd14_2_154 : subd14_2 [-2, 0, -5] = true := by decide +kernel
theorem subd14_2_155 : subd14_2 [-2, 0, -4] = true := by decide +kernel
theorem subd14_2_156 : subd14_2 [-2, 0, -3] = true := by decide +kernel
theorem subd14_2_157 : subd14_2 [-2, 0, -2] = true := by decide +kernel
theorem subd14_2_158 : subd14_2 [-2, 0, -1] = true := by decide +kernel
theorem subd14_2_159 : subd14_2 [-2, 0, 0] = true := by decide +kernel
theorem sbd14_2_4 : ∀ q ∈ blkd14_2_4, subd14_2 q = true := by
  unfold blkd14_2_4
  exact List.forall_mem_cons.2 ⟨subd14_2_128, List.forall_mem_cons.2 ⟨subd14_2_129, List.forall_mem_cons.2 ⟨subd14_2_130, List.forall_mem_cons.2 ⟨subd14_2_131, List.forall_mem_cons.2 ⟨subd14_2_132, List.forall_mem_cons.2 ⟨subd14_2_133, List.forall_mem_cons.2 ⟨subd14_2_134, List.forall_mem_cons.2 ⟨subd14_2_135, List.forall_mem_cons.2 ⟨subd14_2_136, List.forall_mem_cons.2 ⟨subd14_2_137, List.forall_mem_cons.2 ⟨subd14_2_138, List.forall_mem_cons.2 ⟨subd14_2_139, List.forall_mem_cons.2 ⟨subd14_2_140, List.forall_mem_cons.2 ⟨subd14_2_141, List.forall_mem_cons.2 ⟨subd14_2_142, List.forall_mem_cons.2 ⟨subd14_2_143, List.forall_mem_cons.2 ⟨subd14_2_144, List.forall_mem_cons.2 ⟨subd14_2_145, List.forall_mem_cons.2 ⟨subd14_2_146, List.forall_mem_cons.2 ⟨subd14_2_147, List.forall_mem_cons.2 ⟨subd14_2_148, List.forall_mem_cons.2 ⟨subd14_2_149, List.forall_mem_cons.2 ⟨subd14_2_150, List.forall_mem_cons.2 ⟨subd14_2_151, List.forall_mem_cons.2 ⟨subd14_2_152, List.forall_mem_cons.2 ⟨subd14_2_153, List.forall_mem_cons.2 ⟨subd14_2_154, List.forall_mem_cons.2 ⟨subd14_2_155, List.forall_mem_cons.2 ⟨subd14_2_156, List.forall_mem_cons.2 ⟨subd14_2_157, List.forall_mem_cons.2 ⟨subd14_2_158, List.forall_mem_cons.2 ⟨subd14_2_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_160 : subd14_2 [-2, 0, 1] = true := by decide +kernel
theorem subd14_2_161 : subd14_2 [-2, 0, 2] = true := by decide +kernel
theorem subd14_2_162 : subd14_2 [-2, 0, 3] = true := by decide +kernel
theorem subd14_2_163 : subd14_2 [-2, 0, 4] = true := by decide +kernel
theorem subd14_2_164 : subd14_2 [-2, 0, 5] = true := by decide +kernel
theorem subd14_2_165 : subd14_2 [-2, 0, 6] = true := by decide +kernel
theorem subd14_2_166 : subd14_2 [-2, 0, 7] = true := by decide +kernel
theorem subd14_2_167 : subd14_2 [-2, 1, -9] = true := by decide +kernel
theorem subd14_2_168 : subd14_2 [-2, 1, -8] = true := by decide +kernel
theorem subd14_2_169 : subd14_2 [-2, 1, -7] = true := by decide +kernel
theorem subd14_2_170 : subd14_2 [-2, 1, -6] = true := by decide +kernel
theorem subd14_2_171 : subd14_2 [-2, 1, -5] = true := by decide +kernel
theorem subd14_2_172 : subd14_2 [-2, 1, -4] = true := by decide +kernel
theorem subd14_2_173 : subd14_2 [-2, 1, -3] = true := by decide +kernel
theorem subd14_2_174 : subd14_2 [-2, 1, -2] = true := by decide +kernel
theorem subd14_2_175 : subd14_2 [-2, 1, -1] = true := by decide +kernel
theorem subd14_2_176 : subd14_2 [-2, 1, 0] = true := by decide +kernel
theorem subd14_2_177 : subd14_2 [-2, 1, 1] = true := by decide +kernel
theorem subd14_2_178 : subd14_2 [-2, 1, 2] = true := by decide +kernel
theorem subd14_2_179 : subd14_2 [-2, 1, 3] = true := by decide +kernel
theorem subd14_2_180 : subd14_2 [-2, 1, 4] = true := by decide +kernel
theorem subd14_2_181 : subd14_2 [-2, 1, 5] = true := by decide +kernel
theorem subd14_2_182 : subd14_2 [-2, 1, 6] = true := by decide +kernel
theorem subd14_2_183 : subd14_2 [-2, 1, 7] = true := by decide +kernel
theorem subd14_2_184 : subd14_2 [-2, 2, -9] = true := by decide +kernel
theorem subd14_2_185 : subd14_2 [-2, 2, -8] = true := by decide +kernel
theorem subd14_2_186 : subd14_2 [-2, 2, -7] = true := by decide +kernel
theorem subd14_2_187 : subd14_2 [-2, 2, -6] = true := by decide +kernel
theorem subd14_2_188 : subd14_2 [-2, 2, -5] = true := by decide +kernel
theorem subd14_2_189 : subd14_2 [-2, 2, -4] = true := by decide +kernel
theorem subd14_2_190 : subd14_2 [-2, 2, -3] = true := by decide +kernel
theorem subd14_2_191 : subd14_2 [-2, 2, -2] = true := by decide +kernel
theorem sbd14_2_5 : ∀ q ∈ blkd14_2_5, subd14_2 q = true := by
  unfold blkd14_2_5
  exact List.forall_mem_cons.2 ⟨subd14_2_160, List.forall_mem_cons.2 ⟨subd14_2_161, List.forall_mem_cons.2 ⟨subd14_2_162, List.forall_mem_cons.2 ⟨subd14_2_163, List.forall_mem_cons.2 ⟨subd14_2_164, List.forall_mem_cons.2 ⟨subd14_2_165, List.forall_mem_cons.2 ⟨subd14_2_166, List.forall_mem_cons.2 ⟨subd14_2_167, List.forall_mem_cons.2 ⟨subd14_2_168, List.forall_mem_cons.2 ⟨subd14_2_169, List.forall_mem_cons.2 ⟨subd14_2_170, List.forall_mem_cons.2 ⟨subd14_2_171, List.forall_mem_cons.2 ⟨subd14_2_172, List.forall_mem_cons.2 ⟨subd14_2_173, List.forall_mem_cons.2 ⟨subd14_2_174, List.forall_mem_cons.2 ⟨subd14_2_175, List.forall_mem_cons.2 ⟨subd14_2_176, List.forall_mem_cons.2 ⟨subd14_2_177, List.forall_mem_cons.2 ⟨subd14_2_178, List.forall_mem_cons.2 ⟨subd14_2_179, List.forall_mem_cons.2 ⟨subd14_2_180, List.forall_mem_cons.2 ⟨subd14_2_181, List.forall_mem_cons.2 ⟨subd14_2_182, List.forall_mem_cons.2 ⟨subd14_2_183, List.forall_mem_cons.2 ⟨subd14_2_184, List.forall_mem_cons.2 ⟨subd14_2_185, List.forall_mem_cons.2 ⟨subd14_2_186, List.forall_mem_cons.2 ⟨subd14_2_187, List.forall_mem_cons.2 ⟨subd14_2_188, List.forall_mem_cons.2 ⟨subd14_2_189, List.forall_mem_cons.2 ⟨subd14_2_190, List.forall_mem_cons.2 ⟨subd14_2_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
