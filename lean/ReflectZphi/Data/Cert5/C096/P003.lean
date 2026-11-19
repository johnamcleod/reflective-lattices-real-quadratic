import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_0 : subd4_1 [-2] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [2] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-4] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-3, -4] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-3, -3] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-3, -2] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-3, -1] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-3, 0] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-3, 1] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-3, 2] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-3, 3] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [-3, 4] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [-2, -5] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [-2, -4] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [-2, -3] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [-2, -2] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [-2, -1] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [-2, 0] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [-2, 1] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [-2, 2] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [-2, 3] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [-2, 4] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [-1, -5] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [-1, -4] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_26 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_27 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_28 : subd4_2 [-1, 3] = true := by decide +kernel
theorem subd4_2_29 : subd4_2 [-1, 4] = true := by decide +kernel
theorem subd4_2_30 : subd4_2 [0, -5] = true := by decide +kernel
theorem subd4_2_31 : subd4_2 [0, -4] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_cons.2 ⟨subd4_2_26, List.forall_mem_cons.2 ⟨subd4_2_27, List.forall_mem_cons.2 ⟨subd4_2_28, List.forall_mem_cons.2 ⟨subd4_2_29, List.forall_mem_cons.2 ⟨subd4_2_30, List.forall_mem_cons.2 ⟨subd4_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_32 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_33 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_34 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_35 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_36 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_37 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_38 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_39 : subd4_2 [0, 4] = true := by decide +kernel
theorem subd4_2_40 : subd4_2 [1, -5] = true := by decide +kernel
theorem subd4_2_41 : subd4_2 [1, -4] = true := by decide +kernel
theorem subd4_2_42 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_43 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_44 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_45 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_46 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_47 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_48 : subd4_2 [1, 3] = true := by decide +kernel
theorem subd4_2_49 : subd4_2 [1, 4] = true := by decide +kernel
theorem subd4_2_50 : subd4_2 [2, -5] = true := by decide +kernel
theorem subd4_2_51 : subd4_2 [2, -4] = true := by decide +kernel
theorem subd4_2_52 : subd4_2 [2, -3] = true := by decide +kernel
theorem subd4_2_53 : subd4_2 [2, -2] = true := by decide +kernel
theorem subd4_2_54 : subd4_2 [2, -1] = true := by decide +kernel
theorem subd4_2_55 : subd4_2 [2, 0] = true := by decide +kernel
theorem subd4_2_56 : subd4_2 [2, 1] = true := by decide +kernel
theorem subd4_2_57 : subd4_2 [2, 2] = true := by decide +kernel
theorem subd4_2_58 : subd4_2 [2, 3] = true := by decide +kernel
theorem subd4_2_59 : subd4_2 [2, 4] = true := by decide +kernel
theorem subd4_2_60 : subd4_2 [3, -5] = true := by decide +kernel
theorem subd4_2_61 : subd4_2 [3, -4] = true := by decide +kernel
theorem subd4_2_62 : subd4_2 [3, -3] = true := by decide +kernel
theorem subd4_2_63 : subd4_2 [3, -2] = true := by decide +kernel
theorem sbd4_2_1 : ∀ q ∈ blkd4_2_1, subd4_2 q = true := by
  unfold blkd4_2_1
  exact List.forall_mem_cons.2 ⟨subd4_2_32, List.forall_mem_cons.2 ⟨subd4_2_33, List.forall_mem_cons.2 ⟨subd4_2_34, List.forall_mem_cons.2 ⟨subd4_2_35, List.forall_mem_cons.2 ⟨subd4_2_36, List.forall_mem_cons.2 ⟨subd4_2_37, List.forall_mem_cons.2 ⟨subd4_2_38, List.forall_mem_cons.2 ⟨subd4_2_39, List.forall_mem_cons.2 ⟨subd4_2_40, List.forall_mem_cons.2 ⟨subd4_2_41, List.forall_mem_cons.2 ⟨subd4_2_42, List.forall_mem_cons.2 ⟨subd4_2_43, List.forall_mem_cons.2 ⟨subd4_2_44, List.forall_mem_cons.2 ⟨subd4_2_45, List.forall_mem_cons.2 ⟨subd4_2_46, List.forall_mem_cons.2 ⟨subd4_2_47, List.forall_mem_cons.2 ⟨subd4_2_48, List.forall_mem_cons.2 ⟨subd4_2_49, List.forall_mem_cons.2 ⟨subd4_2_50, List.forall_mem_cons.2 ⟨subd4_2_51, List.forall_mem_cons.2 ⟨subd4_2_52, List.forall_mem_cons.2 ⟨subd4_2_53, List.forall_mem_cons.2 ⟨subd4_2_54, List.forall_mem_cons.2 ⟨subd4_2_55, List.forall_mem_cons.2 ⟨subd4_2_56, List.forall_mem_cons.2 ⟨subd4_2_57, List.forall_mem_cons.2 ⟨subd4_2_58, List.forall_mem_cons.2 ⟨subd4_2_59, List.forall_mem_cons.2 ⟨subd4_2_60, List.forall_mem_cons.2 ⟨subd4_2_61, List.forall_mem_cons.2 ⟨subd4_2_62, List.forall_mem_cons.2 ⟨subd4_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_64 : subd4_2 [3, -1] = true := by decide +kernel
theorem subd4_2_65 : subd4_2 [3, 0] = true := by decide +kernel
theorem subd4_2_66 : subd4_2 [3, 1] = true := by decide +kernel
theorem subd4_2_67 : subd4_2 [3, 2] = true := by decide +kernel
theorem subd4_2_68 : subd4_2 [3, 3] = true := by decide +kernel
theorem subd4_2_69 : subd4_2 [4] = true := by decide +kernel
theorem sbd4_2_2 : ∀ q ∈ blkd4_2_2, subd4_2 q = true := by
  unfold blkd4_2_2
  exact List.forall_mem_cons.2 ⟨subd4_2_64, List.forall_mem_cons.2 ⟨subd4_2_65, List.forall_mem_cons.2 ⟨subd4_2_66, List.forall_mem_cons.2 ⟨subd4_2_67, List.forall_mem_cons.2 ⟨subd4_2_68, List.forall_mem_cons.2 ⟨subd4_2_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-2, -3] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-2, -2] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-2, -1] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-2, 0] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-2, 1] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [0, 0, -7] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [0, 0, -6] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [0, 0, -5] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [0, 0, -4] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [0, 0, -3] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [0, 0, -2] = true := by decide +kernel
theorem subd4_3_20 : subd4_3 [0, 0, -1] = true := by decide +kernel
theorem subd4_3_21 : subd4_3 [0, 0, 0] = true := by decide +kernel
theorem subd4_3_22 : subd4_3 [0, 0, 1] = true := by decide +kernel
theorem subd4_3_23 : subd4_3 [0, 0, 2] = true := by decide +kernel
theorem subd4_3_24 : subd4_3 [0, 0, 3] = true := by decide +kernel
theorem subd4_3_25 : subd4_3 [0, 0, 4] = true := by decide +kernel
theorem subd4_3_26 : subd4_3 [0, 0, 5] = true := by decide +kernel
theorem subd4_3_27 : subd4_3 [0, 0, 6] = true := by decide +kernel
theorem subd4_3_28 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_29 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_30 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_31 : subd4_3 [1, -2] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_cons.2 ⟨subd4_3_20, List.forall_mem_cons.2 ⟨subd4_3_21, List.forall_mem_cons.2 ⟨subd4_3_22, List.forall_mem_cons.2 ⟨subd4_3_23, List.forall_mem_cons.2 ⟨subd4_3_24, List.forall_mem_cons.2 ⟨subd4_3_25, List.forall_mem_cons.2 ⟨subd4_3_26, List.forall_mem_cons.2 ⟨subd4_3_27, List.forall_mem_cons.2 ⟨subd4_3_28, List.forall_mem_cons.2 ⟨subd4_3_29, List.forall_mem_cons.2 ⟨subd4_3_30, List.forall_mem_cons.2 ⟨subd4_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_32 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_33 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_34 : subd4_3 [1, 1] = true := by decide +kernel
theorem subd4_3_35 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_36 : subd4_3 [2, -2] = true := by decide +kernel
theorem subd4_3_37 : subd4_3 [2, -1] = true := by decide +kernel
theorem subd4_3_38 : subd4_3 [2, 0] = true := by decide +kernel
theorem subd4_3_39 : subd4_3 [2, 1] = true := by decide +kernel
theorem subd4_3_40 : subd4_3 [2, 2] = true := by decide +kernel
theorem sbd4_3_1 : ∀ q ∈ blkd4_3_1, subd4_3 q = true := by
  unfold blkd4_3_1
  exact List.forall_mem_cons.2 ⟨subd4_3_32, List.forall_mem_cons.2 ⟨subd4_3_33, List.forall_mem_cons.2 ⟨subd4_3_34, List.forall_mem_cons.2 ⟨subd4_3_35, List.forall_mem_cons.2 ⟨subd4_3_36, List.forall_mem_cons.2 ⟨subd4_3_37, List.forall_mem_cons.2 ⟨subd4_3_38, List.forall_mem_cons.2 ⟨subd4_3_39, List.forall_mem_cons.2 ⟨subd4_3_40, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
