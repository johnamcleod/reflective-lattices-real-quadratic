import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-3] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-2, -2] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [-2, -1] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [-2, 0] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [-2, 1] = true := by decide +kernel
theorem subd3_3_5 : subd3_3 [-2, 2] = true := by decide +kernel
theorem subd3_3_6 : subd3_3 [-2, 3] = true := by decide +kernel
theorem subd3_3_7 : subd3_3 [-1, -3] = true := by decide +kernel
theorem subd3_3_8 : subd3_3 [-1, -2] = true := by decide +kernel
theorem subd3_3_9 : subd3_3 [-1, -1] = true := by decide +kernel
theorem subd3_3_10 : subd3_3 [-1, 0] = true := by decide +kernel
theorem subd3_3_11 : subd3_3 [-1, 1] = true := by decide +kernel
theorem subd3_3_12 : subd3_3 [-1, 2] = true := by decide +kernel
theorem subd3_3_13 : subd3_3 [-1, 3] = true := by decide +kernel
theorem subd3_3_14 : subd3_3 [0, -4] = true := by decide +kernel
theorem subd3_3_15 : subd3_3 [0, -3] = true := by decide +kernel
theorem subd3_3_16 : subd3_3 [0, -2] = true := by decide +kernel
theorem subd3_3_17 : subd3_3 [0, -1] = true := by decide +kernel
theorem subd3_3_18 : subd3_3 [0, 0] = true := by decide +kernel
theorem subd3_3_19 : subd3_3 [0, 1] = true := by decide +kernel
theorem subd3_3_20 : subd3_3 [0, 2] = true := by decide +kernel
theorem subd3_3_21 : subd3_3 [0, 3] = true := by decide +kernel
theorem subd3_3_22 : subd3_3 [1, -4] = true := by decide +kernel
theorem subd3_3_23 : subd3_3 [1, -3] = true := by decide +kernel
theorem subd3_3_24 : subd3_3 [1, -2] = true := by decide +kernel
theorem subd3_3_25 : subd3_3 [1, -1] = true := by decide +kernel
theorem subd3_3_26 : subd3_3 [1, 0] = true := by decide +kernel
theorem subd3_3_27 : subd3_3 [1, 1] = true := by decide +kernel
theorem subd3_3_28 : subd3_3 [1, 2] = true := by decide +kernel
theorem subd3_3_29 : subd3_3 [2, -4] = true := by decide +kernel
theorem subd3_3_30 : subd3_3 [2, -3] = true := by decide +kernel
theorem subd3_3_31 : subd3_3 [2, -2] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_cons.2 ⟨subd3_3_5, List.forall_mem_cons.2 ⟨subd3_3_6, List.forall_mem_cons.2 ⟨subd3_3_7, List.forall_mem_cons.2 ⟨subd3_3_8, List.forall_mem_cons.2 ⟨subd3_3_9, List.forall_mem_cons.2 ⟨subd3_3_10, List.forall_mem_cons.2 ⟨subd3_3_11, List.forall_mem_cons.2 ⟨subd3_3_12, List.forall_mem_cons.2 ⟨subd3_3_13, List.forall_mem_cons.2 ⟨subd3_3_14, List.forall_mem_cons.2 ⟨subd3_3_15, List.forall_mem_cons.2 ⟨subd3_3_16, List.forall_mem_cons.2 ⟨subd3_3_17, List.forall_mem_cons.2 ⟨subd3_3_18, List.forall_mem_cons.2 ⟨subd3_3_19, List.forall_mem_cons.2 ⟨subd3_3_20, List.forall_mem_cons.2 ⟨subd3_3_21, List.forall_mem_cons.2 ⟨subd3_3_22, List.forall_mem_cons.2 ⟨subd3_3_23, List.forall_mem_cons.2 ⟨subd3_3_24, List.forall_mem_cons.2 ⟨subd3_3_25, List.forall_mem_cons.2 ⟨subd3_3_26, List.forall_mem_cons.2 ⟨subd3_3_27, List.forall_mem_cons.2 ⟨subd3_3_28, List.forall_mem_cons.2 ⟨subd3_3_29, List.forall_mem_cons.2 ⟨subd3_3_30, List.forall_mem_cons.2 ⟨subd3_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_3_32 : subd3_3 [2, -1] = true := by decide +kernel
theorem subd3_3_33 : subd3_3 [2, 0] = true := by decide +kernel
theorem subd3_3_34 : subd3_3 [2, 1] = true := by decide +kernel
theorem subd3_3_35 : subd3_3 [3] = true := by decide +kernel
theorem sbd3_3_1 : ∀ q ∈ blkd3_3_1, subd3_3 q = true := by
  unfold blkd3_3_1
  exact List.forall_mem_cons.2 ⟨subd3_3_32, List.forall_mem_cons.2 ⟨subd3_3_33, List.forall_mem_cons.2 ⟨subd3_3_34, List.forall_mem_cons.2 ⟨subd3_3_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-1, -1] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-1, 0, -7] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-1, 0, -6] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-1, 0, -5] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-1, 0, -4] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-1, 0, -3] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-1, 0, -2] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-1, 0, -1] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [-1, 0, 0] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [-1, 0, 1] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [-1, 0, 2] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [-1, 0, 3] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [-1, 0, 4] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [-1, 0, 5] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [-1, 0, 6] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [-1, 1] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [0, -3] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [0, -1, -7] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [0, -1, -6] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [0, -1, -5] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [0, -1, -4] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [0, -1, -3] = true := by decide +kernel
theorem subd3_4_24 : subd3_4 [0, -1, -2] = true := by decide +kernel
theorem subd3_4_25 : subd3_4 [0, -1, -1] = true := by decide +kernel
theorem subd3_4_26 : subd3_4 [0, -1, 0] = true := by decide +kernel
theorem subd3_4_27 : subd3_4 [0, -1, 1] = true := by decide +kernel
theorem subd3_4_28 : subd3_4 [0, -1, 2] = true := by decide +kernel
theorem subd3_4_29 : subd3_4 [0, -1, 3] = true := by decide +kernel
theorem subd3_4_30 : subd3_4 [0, -1, 4] = true := by decide +kernel
theorem subd3_4_31 : subd3_4 [0, -1, 5] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_cons.2 ⟨subd3_4_24, List.forall_mem_cons.2 ⟨subd3_4_25, List.forall_mem_cons.2 ⟨subd3_4_26, List.forall_mem_cons.2 ⟨subd3_4_27, List.forall_mem_cons.2 ⟨subd3_4_28, List.forall_mem_cons.2 ⟨subd3_4_29, List.forall_mem_cons.2 ⟨subd3_4_30, List.forall_mem_cons.2 ⟨subd3_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_32 : subd3_4 [0, -1, 6] = true := by decide +kernel
theorem subd3_4_33 : subd3_4 [0, 0, -8] = true := by decide +kernel
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
theorem subd3_4_48 : subd3_4 [0, 0, 7] = true := by decide +kernel
theorem subd3_4_49 : subd3_4 [0, 1, -7] = true := by decide +kernel
theorem subd3_4_50 : subd3_4 [0, 1, -6] = true := by decide +kernel
theorem subd3_4_51 : subd3_4 [0, 1, -5] = true := by decide +kernel
theorem subd3_4_52 : subd3_4 [0, 1, -4] = true := by decide +kernel
theorem subd3_4_53 : subd3_4 [0, 1, -3] = true := by decide +kernel
theorem subd3_4_54 : subd3_4 [0, 1, -2] = true := by decide +kernel
theorem subd3_4_55 : subd3_4 [0, 1, -1] = true := by decide +kernel
theorem subd3_4_56 : subd3_4 [0, 1, 0] = true := by decide +kernel
theorem subd3_4_57 : subd3_4 [0, 1, 1] = true := by decide +kernel
theorem subd3_4_58 : subd3_4 [0, 1, 2] = true := by decide +kernel
theorem subd3_4_59 : subd3_4 [0, 1, 3] = true := by decide +kernel
theorem subd3_4_60 : subd3_4 [0, 1, 4] = true := by decide +kernel
theorem subd3_4_61 : subd3_4 [0, 1, 5] = true := by decide +kernel
theorem subd3_4_62 : subd3_4 [0, 1, 6] = true := by decide +kernel
theorem subd3_4_63 : subd3_4 [0, 2] = true := by decide +kernel
theorem sbd3_4_1 : ∀ q ∈ blkd3_4_1, subd3_4 q = true := by
  unfold blkd3_4_1
  exact List.forall_mem_cons.2 ⟨subd3_4_32, List.forall_mem_cons.2 ⟨subd3_4_33, List.forall_mem_cons.2 ⟨subd3_4_34, List.forall_mem_cons.2 ⟨subd3_4_35, List.forall_mem_cons.2 ⟨subd3_4_36, List.forall_mem_cons.2 ⟨subd3_4_37, List.forall_mem_cons.2 ⟨subd3_4_38, List.forall_mem_cons.2 ⟨subd3_4_39, List.forall_mem_cons.2 ⟨subd3_4_40, List.forall_mem_cons.2 ⟨subd3_4_41, List.forall_mem_cons.2 ⟨subd3_4_42, List.forall_mem_cons.2 ⟨subd3_4_43, List.forall_mem_cons.2 ⟨subd3_4_44, List.forall_mem_cons.2 ⟨subd3_4_45, List.forall_mem_cons.2 ⟨subd3_4_46, List.forall_mem_cons.2 ⟨subd3_4_47, List.forall_mem_cons.2 ⟨subd3_4_48, List.forall_mem_cons.2 ⟨subd3_4_49, List.forall_mem_cons.2 ⟨subd3_4_50, List.forall_mem_cons.2 ⟨subd3_4_51, List.forall_mem_cons.2 ⟨subd3_4_52, List.forall_mem_cons.2 ⟨subd3_4_53, List.forall_mem_cons.2 ⟨subd3_4_54, List.forall_mem_cons.2 ⟨subd3_4_55, List.forall_mem_cons.2 ⟨subd3_4_56, List.forall_mem_cons.2 ⟨subd3_4_57, List.forall_mem_cons.2 ⟨subd3_4_58, List.forall_mem_cons.2 ⟨subd3_4_59, List.forall_mem_cons.2 ⟨subd3_4_60, List.forall_mem_cons.2 ⟨subd3_4_61, List.forall_mem_cons.2 ⟨subd3_4_62, List.forall_mem_cons.2 ⟨subd3_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_64 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_65 : subd3_4 [1, -1] = true := by decide +kernel
theorem subd3_4_66 : subd3_4 [1, 0, -7] = true := by decide +kernel
theorem subd3_4_67 : subd3_4 [1, 0, -6] = true := by decide +kernel
theorem subd3_4_68 : subd3_4 [1, 0, -5] = true := by decide +kernel
theorem subd3_4_69 : subd3_4 [1, 0, -4] = true := by decide +kernel
theorem subd3_4_70 : subd3_4 [1, 0, -3] = true := by decide +kernel
theorem subd3_4_71 : subd3_4 [1, 0, -2] = true := by decide +kernel
theorem subd3_4_72 : subd3_4 [1, 0, -1] = true := by decide +kernel
theorem subd3_4_73 : subd3_4 [1, 0, 0] = true := by decide +kernel
theorem subd3_4_74 : subd3_4 [1, 0, 1] = true := by decide +kernel
theorem subd3_4_75 : subd3_4 [1, 0, 2] = true := by decide +kernel
theorem subd3_4_76 : subd3_4 [1, 0, 3] = true := by decide +kernel
theorem subd3_4_77 : subd3_4 [1, 0, 4] = true := by decide +kernel
theorem subd3_4_78 : subd3_4 [1, 0, 5] = true := by decide +kernel
theorem subd3_4_79 : subd3_4 [1, 0, 6] = true := by decide +kernel
theorem subd3_4_80 : subd3_4 [1, 1] = true := by decide +kernel
theorem sbd3_4_2 : ∀ q ∈ blkd3_4_2, subd3_4 q = true := by
  unfold blkd3_4_2
  exact List.forall_mem_cons.2 ⟨subd3_4_64, List.forall_mem_cons.2 ⟨subd3_4_65, List.forall_mem_cons.2 ⟨subd3_4_66, List.forall_mem_cons.2 ⟨subd3_4_67, List.forall_mem_cons.2 ⟨subd3_4_68, List.forall_mem_cons.2 ⟨subd3_4_69, List.forall_mem_cons.2 ⟨subd3_4_70, List.forall_mem_cons.2 ⟨subd3_4_71, List.forall_mem_cons.2 ⟨subd3_4_72, List.forall_mem_cons.2 ⟨subd3_4_73, List.forall_mem_cons.2 ⟨subd3_4_74, List.forall_mem_cons.2 ⟨subd3_4_75, List.forall_mem_cons.2 ⟨subd3_4_76, List.forall_mem_cons.2 ⟨subd3_4_77, List.forall_mem_cons.2 ⟨subd3_4_78, List.forall_mem_cons.2 ⟨subd3_4_79, List.forall_mem_cons.2 ⟨subd3_4_80, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_5 : ldCheck G d3_5.U d3_5.ms ldd3_5 = true := by decide +kernel
theorem pre_okd3_5 : subPre G cell3 d3_5 = true := by decide +kernel
theorem subd3_5_0 : subd3_5 [-2] = true := by decide +kernel
theorem subd3_5_1 : subd3_5 [-1, -3] = true := by decide +kernel
theorem subd3_5_2 : subd3_5 [-1, -2] = true := by decide +kernel
theorem subd3_5_3 : subd3_5 [-1, -1] = true := by decide +kernel
theorem subd3_5_4 : subd3_5 [-1, 0] = true := by decide +kernel
theorem subd3_5_5 : subd3_5 [-1, 1] = true := by decide +kernel
theorem subd3_5_6 : subd3_5 [-1, 2] = true := by decide +kernel
theorem subd3_5_7 : subd3_5 [-1, 3] = true := by decide +kernel
theorem subd3_5_8 : subd3_5 [0, -3] = true := by decide +kernel
theorem subd3_5_9 : subd3_5 [0, -2] = true := by decide +kernel
theorem subd3_5_10 : subd3_5 [0, -1] = true := by decide +kernel
theorem subd3_5_11 : subd3_5 [0, 0] = true := by decide +kernel
theorem subd3_5_12 : subd3_5 [0, 1] = true := by decide +kernel
theorem subd3_5_13 : subd3_5 [0, 2] = true := by decide +kernel
theorem subd3_5_14 : subd3_5 [1, -4] = true := by decide +kernel
theorem subd3_5_15 : subd3_5 [1, -3] = true := by decide +kernel
theorem subd3_5_16 : subd3_5 [1, -2] = true := by decide +kernel
theorem subd3_5_17 : subd3_5 [1, -1] = true := by decide +kernel
theorem subd3_5_18 : subd3_5 [1, 0] = true := by decide +kernel
theorem subd3_5_19 : subd3_5 [1, 1] = true := by decide +kernel
theorem subd3_5_20 : subd3_5 [1, 2] = true := by decide +kernel
theorem subd3_5_21 : subd3_5 [2] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_cons.2 ⟨subd3_5_1, List.forall_mem_cons.2 ⟨subd3_5_2, List.forall_mem_cons.2 ⟨subd3_5_3, List.forall_mem_cons.2 ⟨subd3_5_4, List.forall_mem_cons.2 ⟨subd3_5_5, List.forall_mem_cons.2 ⟨subd3_5_6, List.forall_mem_cons.2 ⟨subd3_5_7, List.forall_mem_cons.2 ⟨subd3_5_8, List.forall_mem_cons.2 ⟨subd3_5_9, List.forall_mem_cons.2 ⟨subd3_5_10, List.forall_mem_cons.2 ⟨subd3_5_11, List.forall_mem_cons.2 ⟨subd3_5_12, List.forall_mem_cons.2 ⟨subd3_5_13, List.forall_mem_cons.2 ⟨subd3_5_14, List.forall_mem_cons.2 ⟨subd3_5_15, List.forall_mem_cons.2 ⟨subd3_5_16, List.forall_mem_cons.2 ⟨subd3_5_17, List.forall_mem_cons.2 ⟨subd3_5_18, List.forall_mem_cons.2 ⟨subd3_5_19, List.forall_mem_cons.2 ⟨subd3_5_20, List.forall_mem_cons.2 ⟨subd3_5_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_6 : ldCheck G d3_6.U d3_6.ms ldd3_6 = true := by decide +kernel
theorem pre_okd3_6 : subPre G cell3 d3_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
