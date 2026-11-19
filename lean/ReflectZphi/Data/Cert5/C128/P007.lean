import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_4_0 : subd3_4 [-4] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-3, -3] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-3, -2] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-3, -1] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-3, 0] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-3, 1] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-3, 2] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-3, 3] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-3, 4] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [-2, -4] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [-2, -3] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [-2, -2] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [-2, -1] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [-2, 0] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [-2, 1] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [-2, 2] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [-2, 3] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [-2, 4] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [-1, -5] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [-1, -4] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [-1, -3] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [-1, -1] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [-1, 0] = true := by decide +kernel
theorem subd3_4_24 : subd3_4 [-1, 1] = true := by decide +kernel
theorem subd3_4_25 : subd3_4 [-1, 2] = true := by decide +kernel
theorem subd3_4_26 : subd3_4 [-1, 3] = true := by decide +kernel
theorem subd3_4_27 : subd3_4 [-1, 4] = true := by decide +kernel
theorem subd3_4_28 : subd3_4 [-1, 5] = true := by decide +kernel
theorem subd3_4_29 : subd3_4 [0, -5] = true := by decide +kernel
theorem subd3_4_30 : subd3_4 [0, -4] = true := by decide +kernel
theorem subd3_4_31 : subd3_4 [0, -3] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_cons.2 ⟨subd3_4_24, List.forall_mem_cons.2 ⟨subd3_4_25, List.forall_mem_cons.2 ⟨subd3_4_26, List.forall_mem_cons.2 ⟨subd3_4_27, List.forall_mem_cons.2 ⟨subd3_4_28, List.forall_mem_cons.2 ⟨subd3_4_29, List.forall_mem_cons.2 ⟨subd3_4_30, List.forall_mem_cons.2 ⟨subd3_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_32 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_33 : subd3_4 [0, -1] = true := by decide +kernel
theorem subd3_4_34 : subd3_4 [0, 0, -7] = true := by decide +kernel
theorem subd3_4_35 : subd3_4 [0, 0, -6] = true := by decide +kernel
theorem subd3_4_36 : subd3_4 [0, 0, -5] = true := by decide +kernel
theorem subd3_4_37 : subd3_4 [0, 0, -4] = true := by decide +kernel
theorem subd3_4_38 : subd3_4 [0, 0, -3] = true := by decide +kernel
theorem subd3_4_39 : subd3_4 [0, 0, -2] = true := by decide +kernel
theorem subd3_4_40 : subd3_4 [0, 0, -1] = true := by decide +kernel
theorem subd3_4_41 : subd3_4 [0, 0, 0] = true := by decide +kernel
theorem subd3_4_42 : subd3_4 [0, 0, 1] = true := by decide +kernel
theorem subd3_4_43 : subd3_4 [0, 0, 2] = true := by decide +kernel
theorem subd3_4_44 : subd3_4 [0, 0, 3] = true := by decide +kernel
theorem subd3_4_45 : subd3_4 [0, 0, 4] = true := by decide +kernel
theorem subd3_4_46 : subd3_4 [0, 0, 5] = true := by decide +kernel
theorem subd3_4_47 : subd3_4 [0, 0, 6] = true := by decide +kernel
theorem subd3_4_48 : subd3_4 [0, 1] = true := by decide +kernel
theorem subd3_4_49 : subd3_4 [0, 2] = true := by decide +kernel
theorem subd3_4_50 : subd3_4 [0, 3] = true := by decide +kernel
theorem subd3_4_51 : subd3_4 [0, 4] = true := by decide +kernel
theorem subd3_4_52 : subd3_4 [1, -6] = true := by decide +kernel
theorem subd3_4_53 : subd3_4 [1, -5] = true := by decide +kernel
theorem subd3_4_54 : subd3_4 [1, -4] = true := by decide +kernel
theorem subd3_4_55 : subd3_4 [1, -3] = true := by decide +kernel
theorem subd3_4_56 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_57 : subd3_4 [1, -1] = true := by decide +kernel
theorem subd3_4_58 : subd3_4 [1, 0] = true := by decide +kernel
theorem subd3_4_59 : subd3_4 [1, 1] = true := by decide +kernel
theorem subd3_4_60 : subd3_4 [1, 2] = true := by decide +kernel
theorem subd3_4_61 : subd3_4 [1, 3] = true := by decide +kernel
theorem subd3_4_62 : subd3_4 [1, 4] = true := by decide +kernel
theorem subd3_4_63 : subd3_4 [2, -5] = true := by decide +kernel
theorem sbd3_4_1 : ∀ q ∈ blkd3_4_1, subd3_4 q = true := by
  unfold blkd3_4_1
  exact List.forall_mem_cons.2 ⟨subd3_4_32, List.forall_mem_cons.2 ⟨subd3_4_33, List.forall_mem_cons.2 ⟨subd3_4_34, List.forall_mem_cons.2 ⟨subd3_4_35, List.forall_mem_cons.2 ⟨subd3_4_36, List.forall_mem_cons.2 ⟨subd3_4_37, List.forall_mem_cons.2 ⟨subd3_4_38, List.forall_mem_cons.2 ⟨subd3_4_39, List.forall_mem_cons.2 ⟨subd3_4_40, List.forall_mem_cons.2 ⟨subd3_4_41, List.forall_mem_cons.2 ⟨subd3_4_42, List.forall_mem_cons.2 ⟨subd3_4_43, List.forall_mem_cons.2 ⟨subd3_4_44, List.forall_mem_cons.2 ⟨subd3_4_45, List.forall_mem_cons.2 ⟨subd3_4_46, List.forall_mem_cons.2 ⟨subd3_4_47, List.forall_mem_cons.2 ⟨subd3_4_48, List.forall_mem_cons.2 ⟨subd3_4_49, List.forall_mem_cons.2 ⟨subd3_4_50, List.forall_mem_cons.2 ⟨subd3_4_51, List.forall_mem_cons.2 ⟨subd3_4_52, List.forall_mem_cons.2 ⟨subd3_4_53, List.forall_mem_cons.2 ⟨subd3_4_54, List.forall_mem_cons.2 ⟨subd3_4_55, List.forall_mem_cons.2 ⟨subd3_4_56, List.forall_mem_cons.2 ⟨subd3_4_57, List.forall_mem_cons.2 ⟨subd3_4_58, List.forall_mem_cons.2 ⟨subd3_4_59, List.forall_mem_cons.2 ⟨subd3_4_60, List.forall_mem_cons.2 ⟨subd3_4_61, List.forall_mem_cons.2 ⟨subd3_4_62, List.forall_mem_cons.2 ⟨subd3_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_64 : subd3_4 [2, -4] = true := by decide +kernel
theorem subd3_4_65 : subd3_4 [2, -3] = true := by decide +kernel
theorem subd3_4_66 : subd3_4 [2, -2] = true := by decide +kernel
theorem subd3_4_67 : subd3_4 [2, -1] = true := by decide +kernel
theorem subd3_4_68 : subd3_4 [2, 0] = true := by decide +kernel
theorem subd3_4_69 : subd3_4 [2, 1] = true := by decide +kernel
theorem subd3_4_70 : subd3_4 [2, 2] = true := by decide +kernel
theorem subd3_4_71 : subd3_4 [2, 3] = true := by decide +kernel
theorem subd3_4_72 : subd3_4 [3, -5] = true := by decide +kernel
theorem subd3_4_73 : subd3_4 [3, -4] = true := by decide +kernel
theorem subd3_4_74 : subd3_4 [3, -3] = true := by decide +kernel
theorem subd3_4_75 : subd3_4 [3, -2] = true := by decide +kernel
theorem subd3_4_76 : subd3_4 [3, -1] = true := by decide +kernel
theorem subd3_4_77 : subd3_4 [3, 0] = true := by decide +kernel
theorem subd3_4_78 : subd3_4 [3, 1] = true := by decide +kernel
theorem subd3_4_79 : subd3_4 [3, 2] = true := by decide +kernel
theorem subd3_4_80 : subd3_4 [4] = true := by decide +kernel
theorem sbd3_4_2 : ∀ q ∈ blkd3_4_2, subd3_4 q = true := by
  unfold blkd3_4_2
  exact List.forall_mem_cons.2 ⟨subd3_4_64, List.forall_mem_cons.2 ⟨subd3_4_65, List.forall_mem_cons.2 ⟨subd3_4_66, List.forall_mem_cons.2 ⟨subd3_4_67, List.forall_mem_cons.2 ⟨subd3_4_68, List.forall_mem_cons.2 ⟨subd3_4_69, List.forall_mem_cons.2 ⟨subd3_4_70, List.forall_mem_cons.2 ⟨subd3_4_71, List.forall_mem_cons.2 ⟨subd3_4_72, List.forall_mem_cons.2 ⟨subd3_4_73, List.forall_mem_cons.2 ⟨subd3_4_74, List.forall_mem_cons.2 ⟨subd3_4_75, List.forall_mem_cons.2 ⟨subd3_4_76, List.forall_mem_cons.2 ⟨subd3_4_77, List.forall_mem_cons.2 ⟨subd3_4_78, List.forall_mem_cons.2 ⟨subd3_4_79, List.forall_mem_cons.2 ⟨subd3_4_80, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-3, -2] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [-3, -1] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [-3, 0] = true := by decide +kernel
theorem subd3_5_3 : subd3_5 [-3, 1] = true := by decide +kernel
theorem subd3_5_4 : subd3_5 [-3, 2] = true := by decide +kernel
theorem subd3_5_5 : subd3_5 [-2, -3] = true := by decide +kernel
theorem subd3_5_6 : subd3_5 [-2, -2] = true := by decide +kernel
theorem subd3_5_7 : subd3_5 [-2, -1] = true := by decide +kernel
theorem subd3_5_8 : subd3_5 [-2, 0, -7] = true := by decide +kernel
theorem subd3_5_9 : subd3_5 [-2, 0, -6] = true := by decide +kernel
theorem subd3_5_10 : subd3_5 [-2, 0, -5] = true := by decide +kernel
theorem subd3_5_11 : subd3_5 [-2, 0, -4] = true := by decide +kernel
theorem subd3_5_12 : subd3_5 [-2, 0, -3] = true := by decide +kernel
theorem subd3_5_13 : subd3_5 [-2, 0, -2] = true := by decide +kernel
theorem subd3_5_14 : subd3_5 [-2, 0, -1] = true := by decide +kernel
theorem subd3_5_15 : subd3_5 [-2, 0, 0] = true := by decide +kernel
theorem subd3_5_16 : subd3_5 [-2, 0, 1] = true := by decide +kernel
theorem subd3_5_17 : subd3_5 [-2, 0, 2] = true := by decide +kernel
theorem subd3_5_18 : subd3_5 [-2, 0, 3] = true := by decide +kernel
theorem subd3_5_19 : subd3_5 [-2, 0, 4] = true := by decide +kernel
theorem subd3_5_20 : subd3_5 [-2, 0, 5] = true := by decide +kernel
theorem subd3_5_21 : subd3_5 [-2, 0, 6] = true := by decide +kernel
theorem subd3_5_22 : subd3_5 [-2, 1, -6] = true := by decide +kernel
theorem subd3_5_23 : subd3_5 [-2, 1, -5] = true := by decide +kernel
theorem subd3_5_24 : subd3_5 [-2, 1, -4] = true := by decide +kernel
theorem subd3_5_25 : subd3_5 [-2, 1, -3] = true := by decide +kernel
theorem subd3_5_26 : subd3_5 [-2, 1, -2] = true := by decide +kernel
theorem subd3_5_27 : subd3_5 [-2, 1, -1] = true := by decide +kernel
theorem subd3_5_28 : subd3_5 [-2, 1, 0] = true := by decide +kernel
theorem subd3_5_29 : subd3_5 [-2, 1, 1] = true := by decide +kernel
theorem subd3_5_30 : subd3_5 [-2, 1, 2] = true := by decide +kernel
theorem subd3_5_31 : subd3_5 [-2, 1, 3] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_cons.2 ⟨subd3_5_3, List.forall_mem_cons.2 ⟨subd3_5_4, List.forall_mem_cons.2 ⟨subd3_5_5, List.forall_mem_cons.2 ⟨subd3_5_6, List.forall_mem_cons.2 ⟨subd3_5_7, List.forall_mem_cons.2 ⟨subd3_5_8, List.forall_mem_cons.2 ⟨subd3_5_9, List.forall_mem_cons.2 ⟨subd3_5_10, List.forall_mem_cons.2 ⟨subd3_5_11, List.forall_mem_cons.2 ⟨subd3_5_12, List.forall_mem_cons.2 ⟨subd3_5_13, List.forall_mem_cons.2 ⟨subd3_5_14, List.forall_mem_cons.2 ⟨subd3_5_15, List.forall_mem_cons.2 ⟨subd3_5_16, List.forall_mem_cons.2 ⟨subd3_5_17, List.forall_mem_cons.2 ⟨subd3_5_18, List.forall_mem_cons.2 ⟨subd3_5_19, List.forall_mem_cons.2 ⟨subd3_5_20, List.forall_mem_cons.2 ⟨subd3_5_21, List.forall_mem_cons.2 ⟨subd3_5_22, List.forall_mem_cons.2 ⟨subd3_5_23, List.forall_mem_cons.2 ⟨subd3_5_24, List.forall_mem_cons.2 ⟨subd3_5_25, List.forall_mem_cons.2 ⟨subd3_5_26, List.forall_mem_cons.2 ⟨subd3_5_27, List.forall_mem_cons.2 ⟨subd3_5_28, List.forall_mem_cons.2 ⟨subd3_5_29, List.forall_mem_cons.2 ⟨subd3_5_30, List.forall_mem_cons.2 ⟨subd3_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_5_32 : subd3_5 [-2, 1, 4] = true := by decide +kernel
theorem subd3_5_33 : subd3_5 [-2, 1, 5] = true := by decide +kernel
theorem subd3_5_34 : subd3_5 [-2, 1, 6] = true := by decide +kernel
theorem subd3_5_35 : subd3_5 [-2, 2] = true := by decide +kernel
theorem subd3_5_36 : subd3_5 [-2, 3] = true := by decide +kernel
theorem subd3_5_37 : subd3_5 [-1, -4] = true := by decide +kernel
theorem subd3_5_38 : subd3_5 [-1, -3] = true := by decide +kernel
theorem subd3_5_39 : subd3_5 [-1, -2] = true := by decide +kernel
theorem subd3_5_40 : subd3_5 [-1, -1, -7] = true := by decide +kernel
theorem subd3_5_41 : subd3_5 [-1, -1, -6] = true := by decide +kernel
theorem subd3_5_42 : subd3_5 [-1, -1, -5] = true := by decide +kernel
theorem subd3_5_43 : subd3_5 [-1, -1, -4] = true := by decide +kernel
theorem subd3_5_44 : subd3_5 [-1, -1, -3] = true := by decide +kernel
theorem subd3_5_45 : subd3_5 [-1, -1, -2] = true := by decide +kernel
theorem subd3_5_46 : subd3_5 [-1, -1, -1] = true := by decide +kernel
theorem subd3_5_47 : subd3_5 [-1, -1, 0] = true := by decide +kernel
theorem subd3_5_48 : subd3_5 [-1, -1, 1] = true := by decide +kernel
theorem subd3_5_49 : subd3_5 [-1, -1, 2] = true := by decide +kernel
theorem subd3_5_50 : subd3_5 [-1, -1, 3] = true := by decide +kernel
theorem subd3_5_51 : subd3_5 [-1, -1, 4] = true := by decide +kernel
theorem subd3_5_52 : subd3_5 [-1, -1, 5] = true := by decide +kernel
theorem subd3_5_53 : subd3_5 [-1, -1, 6] = true := by decide +kernel
theorem subd3_5_54 : subd3_5 [-1, -1, 7] = true := by decide +kernel
theorem subd3_5_55 : subd3_5 [-1, 0, -8] = true := by decide +kernel
theorem subd3_5_56 : subd3_5 [-1, 0, -7] = true := by decide +kernel
theorem subd3_5_57 : subd3_5 [-1, 0, -6] = true := by decide +kernel
theorem subd3_5_58 : subd3_5 [-1, 0, -5] = true := by decide +kernel
theorem subd3_5_59 : subd3_5 [-1, 0, -4] = true := by decide +kernel
theorem subd3_5_60 : subd3_5 [-1, 0, -3] = true := by decide +kernel
theorem subd3_5_61 : subd3_5 [-1, 0, -2] = true := by decide +kernel
theorem subd3_5_62 : subd3_5 [-1, 0, -1] = true := by decide +kernel
theorem subd3_5_63 : subd3_5 [-1, 0, 0] = true := by decide +kernel
theorem sbd3_5_1 : ∀ q ∈ blkd3_5_1, subd3_5 q = true := by
  unfold blkd3_5_1
  exact List.forall_mem_cons.2 ⟨subd3_5_32, List.forall_mem_cons.2 ⟨subd3_5_33, List.forall_mem_cons.2 ⟨subd3_5_34, List.forall_mem_cons.2 ⟨subd3_5_35, List.forall_mem_cons.2 ⟨subd3_5_36, List.forall_mem_cons.2 ⟨subd3_5_37, List.forall_mem_cons.2 ⟨subd3_5_38, List.forall_mem_cons.2 ⟨subd3_5_39, List.forall_mem_cons.2 ⟨subd3_5_40, List.forall_mem_cons.2 ⟨subd3_5_41, List.forall_mem_cons.2 ⟨subd3_5_42, List.forall_mem_cons.2 ⟨subd3_5_43, List.forall_mem_cons.2 ⟨subd3_5_44, List.forall_mem_cons.2 ⟨subd3_5_45, List.forall_mem_cons.2 ⟨subd3_5_46, List.forall_mem_cons.2 ⟨subd3_5_47, List.forall_mem_cons.2 ⟨subd3_5_48, List.forall_mem_cons.2 ⟨subd3_5_49, List.forall_mem_cons.2 ⟨subd3_5_50, List.forall_mem_cons.2 ⟨subd3_5_51, List.forall_mem_cons.2 ⟨subd3_5_52, List.forall_mem_cons.2 ⟨subd3_5_53, List.forall_mem_cons.2 ⟨subd3_5_54, List.forall_mem_cons.2 ⟨subd3_5_55, List.forall_mem_cons.2 ⟨subd3_5_56, List.forall_mem_cons.2 ⟨subd3_5_57, List.forall_mem_cons.2 ⟨subd3_5_58, List.forall_mem_cons.2 ⟨subd3_5_59, List.forall_mem_cons.2 ⟨subd3_5_60, List.forall_mem_cons.2 ⟨subd3_5_61, List.forall_mem_cons.2 ⟨subd3_5_62, List.forall_mem_cons.2 ⟨subd3_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
