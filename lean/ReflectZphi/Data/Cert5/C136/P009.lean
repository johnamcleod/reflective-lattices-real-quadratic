import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_0 : subd7_2 [-4] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-3, -3] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-3, -2] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-3, -1] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-3, 0] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-3, 1] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-3, 2] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-3, 3] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-3, 4] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-3, 5] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [-2, -4] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [-2, -3] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [-2, -2] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [-2, -1] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [-2, 0] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [-2, 1] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [-2, 2] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [-2, 3] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [-2, 4] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [-2, 5] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [-1, -5] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [-1, -4] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [-1, -3] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [-1, 1] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [-1, 2] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [-1, 3] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [-1, 4] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [-1, 5] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [0, -6] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_32 : subd7_2 [0, -5] = true := by decide +kernel
theorem subd7_2_33 : subd7_2 [0, -4] = true := by decide +kernel
theorem subd7_2_34 : subd7_2 [0, -3] = true := by decide +kernel
theorem subd7_2_35 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_36 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_37 : subd7_2 [0, 0] = true := by decide +kernel
theorem subd7_2_38 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_39 : subd7_2 [0, 2] = true := by decide +kernel
theorem subd7_2_40 : subd7_2 [0, 3] = true := by decide +kernel
theorem subd7_2_41 : subd7_2 [0, 4] = true := by decide +kernel
theorem subd7_2_42 : subd7_2 [0, 5] = true := by decide +kernel
theorem subd7_2_43 : subd7_2 [1, -6] = true := by decide +kernel
theorem subd7_2_44 : subd7_2 [1, -5] = true := by decide +kernel
theorem subd7_2_45 : subd7_2 [1, -4] = true := by decide +kernel
theorem subd7_2_46 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_47 : subd7_2 [1, -2] = true := by decide +kernel
theorem subd7_2_48 : subd7_2 [1, -1] = true := by decide +kernel
theorem subd7_2_49 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_50 : subd7_2 [1, 1] = true := by decide +kernel
theorem subd7_2_51 : subd7_2 [1, 2] = true := by decide +kernel
theorem subd7_2_52 : subd7_2 [1, 3] = true := by decide +kernel
theorem subd7_2_53 : subd7_2 [1, 4] = true := by decide +kernel
theorem subd7_2_54 : subd7_2 [2, -6] = true := by decide +kernel
theorem subd7_2_55 : subd7_2 [2, -5] = true := by decide +kernel
theorem subd7_2_56 : subd7_2 [2, -4] = true := by decide +kernel
theorem subd7_2_57 : subd7_2 [2, -3] = true := by decide +kernel
theorem subd7_2_58 : subd7_2 [2, -2] = true := by decide +kernel
theorem subd7_2_59 : subd7_2 [2, -1] = true := by decide +kernel
theorem subd7_2_60 : subd7_2 [2, 0] = true := by decide +kernel
theorem subd7_2_61 : subd7_2 [2, 1] = true := by decide +kernel
theorem subd7_2_62 : subd7_2 [2, 2] = true := by decide +kernel
theorem subd7_2_63 : subd7_2 [2, 3] = true := by decide +kernel
theorem sbd7_2_1 : ∀ q ∈ blkd7_2_1, subd7_2 q = true := by
  unfold blkd7_2_1
  exact List.forall_mem_cons.2 ⟨subd7_2_32, List.forall_mem_cons.2 ⟨subd7_2_33, List.forall_mem_cons.2 ⟨subd7_2_34, List.forall_mem_cons.2 ⟨subd7_2_35, List.forall_mem_cons.2 ⟨subd7_2_36, List.forall_mem_cons.2 ⟨subd7_2_37, List.forall_mem_cons.2 ⟨subd7_2_38, List.forall_mem_cons.2 ⟨subd7_2_39, List.forall_mem_cons.2 ⟨subd7_2_40, List.forall_mem_cons.2 ⟨subd7_2_41, List.forall_mem_cons.2 ⟨subd7_2_42, List.forall_mem_cons.2 ⟨subd7_2_43, List.forall_mem_cons.2 ⟨subd7_2_44, List.forall_mem_cons.2 ⟨subd7_2_45, List.forall_mem_cons.2 ⟨subd7_2_46, List.forall_mem_cons.2 ⟨subd7_2_47, List.forall_mem_cons.2 ⟨subd7_2_48, List.forall_mem_cons.2 ⟨subd7_2_49, List.forall_mem_cons.2 ⟨subd7_2_50, List.forall_mem_cons.2 ⟨subd7_2_51, List.forall_mem_cons.2 ⟨subd7_2_52, List.forall_mem_cons.2 ⟨subd7_2_53, List.forall_mem_cons.2 ⟨subd7_2_54, List.forall_mem_cons.2 ⟨subd7_2_55, List.forall_mem_cons.2 ⟨subd7_2_56, List.forall_mem_cons.2 ⟨subd7_2_57, List.forall_mem_cons.2 ⟨subd7_2_58, List.forall_mem_cons.2 ⟨subd7_2_59, List.forall_mem_cons.2 ⟨subd7_2_60, List.forall_mem_cons.2 ⟨subd7_2_61, List.forall_mem_cons.2 ⟨subd7_2_62, List.forall_mem_cons.2 ⟨subd7_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_64 : subd7_2 [3, -6] = true := by decide +kernel
theorem subd7_2_65 : subd7_2 [3, -5] = true := by decide +kernel
theorem subd7_2_66 : subd7_2 [3, -4] = true := by decide +kernel
theorem subd7_2_67 : subd7_2 [3, -3] = true := by decide +kernel
theorem subd7_2_68 : subd7_2 [3, -2] = true := by decide +kernel
theorem subd7_2_69 : subd7_2 [3, -1] = true := by decide +kernel
theorem subd7_2_70 : subd7_2 [3, 0] = true := by decide +kernel
theorem subd7_2_71 : subd7_2 [3, 1] = true := by decide +kernel
theorem subd7_2_72 : subd7_2 [3, 2] = true := by decide +kernel
theorem subd7_2_73 : subd7_2 [4] = true := by decide +kernel
theorem sbd7_2_2 : ∀ q ∈ blkd7_2_2, subd7_2 q = true := by
  unfold blkd7_2_2
  exact List.forall_mem_cons.2 ⟨subd7_2_64, List.forall_mem_cons.2 ⟨subd7_2_65, List.forall_mem_cons.2 ⟨subd7_2_66, List.forall_mem_cons.2 ⟨subd7_2_67, List.forall_mem_cons.2 ⟨subd7_2_68, List.forall_mem_cons.2 ⟨subd7_2_69, List.forall_mem_cons.2 ⟨subd7_2_70, List.forall_mem_cons.2 ⟨subd7_2_71, List.forall_mem_cons.2 ⟨subd7_2_72, List.forall_mem_cons.2 ⟨subd7_2_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-4] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-3, -4] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-3, -3] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-3, -2] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-3, -1] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-3, 0] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-3, 1] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-3, 2] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-3, 3] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-2, -5] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-2, -4] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-2, -3] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-2, -1] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-2, 0] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-2, 1] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-2, 2] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-2, 3] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-1, -5] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-1, -4] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-1, -1, -6] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-1, -1, -5] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-1, -1, -4] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-1, -1, -3] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-1, -1, -2] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-1, -1, -1] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-1, -1, 0] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-1, -1, 1] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-1, -1, 2] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-1, -1, 3] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-1, -1, 4] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-1, -1, 5] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-1, -1, 6] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-1, -1, 7] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [-1, 0, -7] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [-1, 0, -6] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [-1, 0, -5] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [-1, 0, -4] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [-1, 0, -3] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [-1, 0, -2] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [-1, 0, -1] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [-1, 0, 0] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [-1, 0, 1] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [-1, 0, 2] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [-1, 0, 3] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [-1, 0, 4] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [-1, 0, 5] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [-1, 0, 6] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [-1, 1, -7] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [-1, 1, -6] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [-1, 1, -5] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [-1, 1, -4] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [-1, 1, -3] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [-1, 1, -2] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [-1, 1, -1] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [-1, 1, 0] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [-1, 1, 1] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [-1, 1, 2] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [-1, 1, 3] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [-1, 1, 4] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [-1, 1, 5] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [-1, 1, 6] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C136
