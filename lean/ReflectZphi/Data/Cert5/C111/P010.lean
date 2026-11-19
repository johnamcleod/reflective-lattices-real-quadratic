import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_0 : subd7_0 [-3] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-2] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [2] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [3] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-5] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-4, -5] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-4, -4] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-4, -3] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-4, -2] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-4, -1] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-4, 0] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-4, 1] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-4, 2] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-3, -5] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-3, -4] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-3, -3] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-3, -2] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-3, -1] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-3, 0] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-3, 1] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [-3, 2] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [-3, 3] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [-2, -5] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [-2, -4] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [-2, -2] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [-2, -1] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [-2, 0] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [-2, 1] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [-2, 2] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [-2, 3] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [-1, -5] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [-1, -1] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [-1, 3] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [-1, 4] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [0, -5] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_40 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_41 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_42 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_43 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_44 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_45 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_46 : subd7_1 [0, 4] = true := by decide +kernel
theorem subd7_1_47 : subd7_1 [1, -5] = true := by decide +kernel
theorem subd7_1_48 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_49 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_50 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_51 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_52 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_53 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_54 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_55 : subd7_1 [1, 3] = true := by decide +kernel
theorem subd7_1_56 : subd7_1 [1, 4] = true := by decide +kernel
theorem subd7_1_57 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_58 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_59 : subd7_1 [2, -2] = true := by decide +kernel
theorem subd7_1_60 : subd7_1 [2, -1] = true := by decide +kernel
theorem subd7_1_61 : subd7_1 [2, 0] = true := by decide +kernel
theorem subd7_1_62 : subd7_1 [2, 1] = true := by decide +kernel
theorem subd7_1_63 : subd7_1 [2, 2] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_cons.2 ⟨subd7_1_40, List.forall_mem_cons.2 ⟨subd7_1_41, List.forall_mem_cons.2 ⟨subd7_1_42, List.forall_mem_cons.2 ⟨subd7_1_43, List.forall_mem_cons.2 ⟨subd7_1_44, List.forall_mem_cons.2 ⟨subd7_1_45, List.forall_mem_cons.2 ⟨subd7_1_46, List.forall_mem_cons.2 ⟨subd7_1_47, List.forall_mem_cons.2 ⟨subd7_1_48, List.forall_mem_cons.2 ⟨subd7_1_49, List.forall_mem_cons.2 ⟨subd7_1_50, List.forall_mem_cons.2 ⟨subd7_1_51, List.forall_mem_cons.2 ⟨subd7_1_52, List.forall_mem_cons.2 ⟨subd7_1_53, List.forall_mem_cons.2 ⟨subd7_1_54, List.forall_mem_cons.2 ⟨subd7_1_55, List.forall_mem_cons.2 ⟨subd7_1_56, List.forall_mem_cons.2 ⟨subd7_1_57, List.forall_mem_cons.2 ⟨subd7_1_58, List.forall_mem_cons.2 ⟨subd7_1_59, List.forall_mem_cons.2 ⟨subd7_1_60, List.forall_mem_cons.2 ⟨subd7_1_61, List.forall_mem_cons.2 ⟨subd7_1_62, List.forall_mem_cons.2 ⟨subd7_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_64 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_65 : subd7_1 [2, 4] = true := by decide +kernel
theorem subd7_1_66 : subd7_1 [3, -4] = true := by decide +kernel
theorem subd7_1_67 : subd7_1 [3, -3] = true := by decide +kernel
theorem subd7_1_68 : subd7_1 [3, -2] = true := by decide +kernel
theorem subd7_1_69 : subd7_1 [3, -1] = true := by decide +kernel
theorem subd7_1_70 : subd7_1 [3, 0] = true := by decide +kernel
theorem subd7_1_71 : subd7_1 [3, 1] = true := by decide +kernel
theorem subd7_1_72 : subd7_1 [3, 2] = true := by decide +kernel
theorem subd7_1_73 : subd7_1 [3, 3] = true := by decide +kernel
theorem subd7_1_74 : subd7_1 [3, 4] = true := by decide +kernel
theorem subd7_1_75 : subd7_1 [4, -3] = true := by decide +kernel
theorem subd7_1_76 : subd7_1 [4, -2] = true := by decide +kernel
theorem subd7_1_77 : subd7_1 [4, -1] = true := by decide +kernel
theorem subd7_1_78 : subd7_1 [4, 0] = true := by decide +kernel
theorem subd7_1_79 : subd7_1 [4, 1] = true := by decide +kernel
theorem subd7_1_80 : subd7_1 [4, 2] = true := by decide +kernel
theorem subd7_1_81 : subd7_1 [4, 3] = true := by decide +kernel
theorem subd7_1_82 : subd7_1 [4, 4] = true := by decide +kernel
theorem subd7_1_83 : subd7_1 [5] = true := by decide +kernel
theorem sbd7_1_2 : ∀ q ∈ blkd7_1_2, subd7_1 q = true := by
  unfold blkd7_1_2
  exact List.forall_mem_cons.2 ⟨subd7_1_64, List.forall_mem_cons.2 ⟨subd7_1_65, List.forall_mem_cons.2 ⟨subd7_1_66, List.forall_mem_cons.2 ⟨subd7_1_67, List.forall_mem_cons.2 ⟨subd7_1_68, List.forall_mem_cons.2 ⟨subd7_1_69, List.forall_mem_cons.2 ⟨subd7_1_70, List.forall_mem_cons.2 ⟨subd7_1_71, List.forall_mem_cons.2 ⟨subd7_1_72, List.forall_mem_cons.2 ⟨subd7_1_73, List.forall_mem_cons.2 ⟨subd7_1_74, List.forall_mem_cons.2 ⟨subd7_1_75, List.forall_mem_cons.2 ⟨subd7_1_76, List.forall_mem_cons.2 ⟨subd7_1_77, List.forall_mem_cons.2 ⟨subd7_1_78, List.forall_mem_cons.2 ⟨subd7_1_79, List.forall_mem_cons.2 ⟨subd7_1_80, List.forall_mem_cons.2 ⟨subd7_1_81, List.forall_mem_cons.2 ⟨subd7_1_82, List.forall_mem_cons.2 ⟨subd7_1_83, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-4] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-3, -3] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-3, -2] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-3, -1, -6] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-3, -1, -5] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-3, -1, -4] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-3, -1, -3] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-3, -1, -2] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-3, -1, -1] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-3, -1, 0] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [-3, -1, 1] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [-3, -1, 2] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [-3, -1, 3] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [-3, -1, 4] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [-3, -1, 5] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [-3, -1, 6] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [-3, -1, 7] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [-3, 0, -6] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [-3, 0, -5] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [-3, 0, -4] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [-3, 0, -3] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [-3, 0, -2] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [-3, 0, -1] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [-3, 0, 0] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [-3, 0, 1] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [-3, 0, 2] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [-3, 0, 3] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [-3, 0, 4] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [-3, 0, 5] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [-3, 0, 6] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [-3, 0, 7] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [-3, 0, 8] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_32 : subd7_2 [-3, 1, -6] = true := by decide +kernel
theorem subd7_2_33 : subd7_2 [-3, 1, -5] = true := by decide +kernel
theorem subd7_2_34 : subd7_2 [-3, 1, -4] = true := by decide +kernel
theorem subd7_2_35 : subd7_2 [-3, 1, -3] = true := by decide +kernel
theorem subd7_2_36 : subd7_2 [-3, 1, -2] = true := by decide +kernel
theorem subd7_2_37 : subd7_2 [-3, 1, -1] = true := by decide +kernel
theorem subd7_2_38 : subd7_2 [-3, 1, 0] = true := by decide +kernel
theorem subd7_2_39 : subd7_2 [-3, 1, 1] = true := by decide +kernel
theorem subd7_2_40 : subd7_2 [-3, 1, 2] = true := by decide +kernel
theorem subd7_2_41 : subd7_2 [-3, 1, 3] = true := by decide +kernel
theorem subd7_2_42 : subd7_2 [-3, 1, 4] = true := by decide +kernel
theorem subd7_2_43 : subd7_2 [-3, 1, 5] = true := by decide +kernel
theorem subd7_2_44 : subd7_2 [-3, 1, 6] = true := by decide +kernel
theorem subd7_2_45 : subd7_2 [-3, 1, 7] = true := by decide +kernel
theorem subd7_2_46 : subd7_2 [-3, 1, 8] = true := by decide +kernel
theorem subd7_2_47 : subd7_2 [-3, 1, 9] = true := by decide +kernel
theorem subd7_2_48 : subd7_2 [-3, 2, -5] = true := by decide +kernel
theorem subd7_2_49 : subd7_2 [-3, 2, -4] = true := by decide +kernel
theorem subd7_2_50 : subd7_2 [-3, 2, -3] = true := by decide +kernel
theorem subd7_2_51 : subd7_2 [-3, 2, -2] = true := by decide +kernel
theorem subd7_2_52 : subd7_2 [-3, 2, -1] = true := by decide +kernel
theorem subd7_2_53 : subd7_2 [-3, 2, 0] = true := by decide +kernel
theorem subd7_2_54 : subd7_2 [-3, 2, 1] = true := by decide +kernel
theorem subd7_2_55 : subd7_2 [-3, 2, 2] = true := by decide +kernel
theorem subd7_2_56 : subd7_2 [-3, 2, 3] = true := by decide +kernel
theorem subd7_2_57 : subd7_2 [-3, 2, 4] = true := by decide +kernel
theorem subd7_2_58 : subd7_2 [-3, 2, 5] = true := by decide +kernel
theorem subd7_2_59 : subd7_2 [-3, 2, 6] = true := by decide +kernel
theorem subd7_2_60 : subd7_2 [-3, 2, 7] = true := by decide +kernel
theorem subd7_2_61 : subd7_2 [-3, 2, 8] = true := by decide +kernel
theorem subd7_2_62 : subd7_2 [-3, 3] = true := by decide +kernel
theorem subd7_2_63 : subd7_2 [-2, -4] = true := by decide +kernel
theorem sbd7_2_1 : ∀ q ∈ blkd7_2_1, subd7_2 q = true := by
  unfold blkd7_2_1
  exact List.forall_mem_cons.2 ⟨subd7_2_32, List.forall_mem_cons.2 ⟨subd7_2_33, List.forall_mem_cons.2 ⟨subd7_2_34, List.forall_mem_cons.2 ⟨subd7_2_35, List.forall_mem_cons.2 ⟨subd7_2_36, List.forall_mem_cons.2 ⟨subd7_2_37, List.forall_mem_cons.2 ⟨subd7_2_38, List.forall_mem_cons.2 ⟨subd7_2_39, List.forall_mem_cons.2 ⟨subd7_2_40, List.forall_mem_cons.2 ⟨subd7_2_41, List.forall_mem_cons.2 ⟨subd7_2_42, List.forall_mem_cons.2 ⟨subd7_2_43, List.forall_mem_cons.2 ⟨subd7_2_44, List.forall_mem_cons.2 ⟨subd7_2_45, List.forall_mem_cons.2 ⟨subd7_2_46, List.forall_mem_cons.2 ⟨subd7_2_47, List.forall_mem_cons.2 ⟨subd7_2_48, List.forall_mem_cons.2 ⟨subd7_2_49, List.forall_mem_cons.2 ⟨subd7_2_50, List.forall_mem_cons.2 ⟨subd7_2_51, List.forall_mem_cons.2 ⟨subd7_2_52, List.forall_mem_cons.2 ⟨subd7_2_53, List.forall_mem_cons.2 ⟨subd7_2_54, List.forall_mem_cons.2 ⟨subd7_2_55, List.forall_mem_cons.2 ⟨subd7_2_56, List.forall_mem_cons.2 ⟨subd7_2_57, List.forall_mem_cons.2 ⟨subd7_2_58, List.forall_mem_cons.2 ⟨subd7_2_59, List.forall_mem_cons.2 ⟨subd7_2_60, List.forall_mem_cons.2 ⟨subd7_2_61, List.forall_mem_cons.2 ⟨subd7_2_62, List.forall_mem_cons.2 ⟨subd7_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_64 : subd7_2 [-2, -3] = true := by decide +kernel
theorem subd7_2_65 : subd7_2 [-2, -2, -8] = true := by decide +kernel
theorem subd7_2_66 : subd7_2 [-2, -2, -7] = true := by decide +kernel
theorem subd7_2_67 : subd7_2 [-2, -2, -6] = true := by decide +kernel
theorem subd7_2_68 : subd7_2 [-2, -2, -5] = true := by decide +kernel
theorem subd7_2_69 : subd7_2 [-2, -2, -4] = true := by decide +kernel
theorem subd7_2_70 : subd7_2 [-2, -2, -3] = true := by decide +kernel
theorem subd7_2_71 : subd7_2 [-2, -2, -2] = true := by decide +kernel
theorem subd7_2_72 : subd7_2 [-2, -2, -1] = true := by decide +kernel
theorem subd7_2_73 : subd7_2 [-2, -2, 0] = true := by decide +kernel
theorem subd7_2_74 : subd7_2 [-2, -2, 1] = true := by decide +kernel
theorem subd7_2_75 : subd7_2 [-2, -2, 2] = true := by decide +kernel
theorem subd7_2_76 : subd7_2 [-2, -2, 3] = true := by decide +kernel
theorem subd7_2_77 : subd7_2 [-2, -2, 4] = true := by decide +kernel
theorem subd7_2_78 : subd7_2 [-2, -2, 5] = true := by decide +kernel
theorem subd7_2_79 : subd7_2 [-2, -2, 6] = true := by decide +kernel
theorem subd7_2_80 : subd7_2 [-2, -2, 7] = true := by decide +kernel
theorem subd7_2_81 : subd7_2 [-2, -1, -9] = true := by decide +kernel
theorem subd7_2_82 : subd7_2 [-2, -1, -8] = true := by decide +kernel
theorem subd7_2_83 : subd7_2 [-2, -1, -7] = true := by decide +kernel
theorem subd7_2_84 : subd7_2 [-2, -1, -6] = true := by decide +kernel
theorem subd7_2_85 : subd7_2 [-2, -1, -5] = true := by decide +kernel
theorem subd7_2_86 : subd7_2 [-2, -1, -4] = true := by decide +kernel
theorem subd7_2_87 : subd7_2 [-2, -1, -3] = true := by decide +kernel
theorem subd7_2_88 : subd7_2 [-2, -1, -2] = true := by decide +kernel
theorem subd7_2_89 : subd7_2 [-2, -1, -1] = true := by decide +kernel
theorem subd7_2_90 : subd7_2 [-2, -1, 0] = true := by decide +kernel
theorem subd7_2_91 : subd7_2 [-2, -1, 1] = true := by decide +kernel
theorem subd7_2_92 : subd7_2 [-2, -1, 2] = true := by decide +kernel
theorem subd7_2_93 : subd7_2 [-2, -1, 3] = true := by decide +kernel
theorem subd7_2_94 : subd7_2 [-2, -1, 4] = true := by decide +kernel
theorem subd7_2_95 : subd7_2 [-2, -1, 5] = true := by decide +kernel
theorem sbd7_2_2 : ∀ q ∈ blkd7_2_2, subd7_2 q = true := by
  unfold blkd7_2_2
  exact List.forall_mem_cons.2 ⟨subd7_2_64, List.forall_mem_cons.2 ⟨subd7_2_65, List.forall_mem_cons.2 ⟨subd7_2_66, List.forall_mem_cons.2 ⟨subd7_2_67, List.forall_mem_cons.2 ⟨subd7_2_68, List.forall_mem_cons.2 ⟨subd7_2_69, List.forall_mem_cons.2 ⟨subd7_2_70, List.forall_mem_cons.2 ⟨subd7_2_71, List.forall_mem_cons.2 ⟨subd7_2_72, List.forall_mem_cons.2 ⟨subd7_2_73, List.forall_mem_cons.2 ⟨subd7_2_74, List.forall_mem_cons.2 ⟨subd7_2_75, List.forall_mem_cons.2 ⟨subd7_2_76, List.forall_mem_cons.2 ⟨subd7_2_77, List.forall_mem_cons.2 ⟨subd7_2_78, List.forall_mem_cons.2 ⟨subd7_2_79, List.forall_mem_cons.2 ⟨subd7_2_80, List.forall_mem_cons.2 ⟨subd7_2_81, List.forall_mem_cons.2 ⟨subd7_2_82, List.forall_mem_cons.2 ⟨subd7_2_83, List.forall_mem_cons.2 ⟨subd7_2_84, List.forall_mem_cons.2 ⟨subd7_2_85, List.forall_mem_cons.2 ⟨subd7_2_86, List.forall_mem_cons.2 ⟨subd7_2_87, List.forall_mem_cons.2 ⟨subd7_2_88, List.forall_mem_cons.2 ⟨subd7_2_89, List.forall_mem_cons.2 ⟨subd7_2_90, List.forall_mem_cons.2 ⟨subd7_2_91, List.forall_mem_cons.2 ⟨subd7_2_92, List.forall_mem_cons.2 ⟨subd7_2_93, List.forall_mem_cons.2 ⟨subd7_2_94, List.forall_mem_cons.2 ⟨subd7_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
