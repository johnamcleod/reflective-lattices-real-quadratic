import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_32 : subd10_2 [0, -5] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [0, -4] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [0, 3] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [0, 4] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [0, 5] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [1, -5] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [1, -4] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [1, 4] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [1, 5] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [2, -4] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [2, -1] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [2, 0] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [2, 3] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [2, 4] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [2, 5] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [3, -3] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [3, -2] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [3, -1] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [3, 0] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [3, 1] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [3, 2] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [3, 3] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [3, 4] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [3, 5] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [4] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-3] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-2, -1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-2, 0] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-2, 1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-2, 2] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-1, 3] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [0, 3] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [1, -4] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [2, -4] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [2, -3] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [2, -2] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [2, -1] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [2, 0] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [2, 1] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [3] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-3, -3] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-3, -2] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-3, -1] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-3, 0] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-3, 1] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-3, 2] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-2, -4] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-2, -3] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-2, -2] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-2, -1] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [-2, 0] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [-2, 1] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [-2, 2] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [-2, 3] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [-1, -4] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [-1, -1, -7] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [-1, -1, -6] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [-1, -1, -5] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [-1, -1, -4] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [-1, -1, -3] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [-1, -1, -2] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [-1, -1, -1] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [-1, -1, 0] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [-1, -1, 1] = true := by decide +kernel
theorem subd10_4_26 : subd10_4 [-1, -1, 2] = true := by decide +kernel
theorem subd10_4_27 : subd10_4 [-1, -1, 3] = true := by decide +kernel
theorem subd10_4_28 : subd10_4 [-1, -1, 4] = true := by decide +kernel
theorem subd10_4_29 : subd10_4 [-1, -1, 5] = true := by decide +kernel
theorem subd10_4_30 : subd10_4 [-1, -1, 6] = true := by decide +kernel
theorem subd10_4_31 : subd10_4 [-1, 0, -8] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_cons.2 ⟨subd10_4_26, List.forall_mem_cons.2 ⟨subd10_4_27, List.forall_mem_cons.2 ⟨subd10_4_28, List.forall_mem_cons.2 ⟨subd10_4_29, List.forall_mem_cons.2 ⟨subd10_4_30, List.forall_mem_cons.2 ⟨subd10_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_32 : subd10_4 [-1, 0, -7] = true := by decide +kernel
theorem subd10_4_33 : subd10_4 [-1, 0, -6] = true := by decide +kernel
theorem subd10_4_34 : subd10_4 [-1, 0, -5] = true := by decide +kernel
theorem subd10_4_35 : subd10_4 [-1, 0, -4] = true := by decide +kernel
theorem subd10_4_36 : subd10_4 [-1, 0, -3] = true := by decide +kernel
theorem subd10_4_37 : subd10_4 [-1, 0, -2] = true := by decide +kernel
theorem subd10_4_38 : subd10_4 [-1, 0, -1] = true := by decide +kernel
theorem subd10_4_39 : subd10_4 [-1, 0, 0] = true := by decide +kernel
theorem subd10_4_40 : subd10_4 [-1, 0, 1] = true := by decide +kernel
theorem subd10_4_41 : subd10_4 [-1, 0, 2] = true := by decide +kernel
theorem subd10_4_42 : subd10_4 [-1, 0, 3] = true := by decide +kernel
theorem subd10_4_43 : subd10_4 [-1, 0, 4] = true := by decide +kernel
theorem subd10_4_44 : subd10_4 [-1, 0, 5] = true := by decide +kernel
theorem subd10_4_45 : subd10_4 [-1, 0, 6] = true := by decide +kernel
theorem subd10_4_46 : subd10_4 [-1, 1, -7] = true := by decide +kernel
theorem subd10_4_47 : subd10_4 [-1, 1, -6] = true := by decide +kernel
theorem subd10_4_48 : subd10_4 [-1, 1, -5] = true := by decide +kernel
theorem subd10_4_49 : subd10_4 [-1, 1, -4] = true := by decide +kernel
theorem subd10_4_50 : subd10_4 [-1, 1, -3] = true := by decide +kernel
theorem subd10_4_51 : subd10_4 [-1, 1, -2] = true := by decide +kernel
theorem subd10_4_52 : subd10_4 [-1, 1, -1] = true := by decide +kernel
theorem subd10_4_53 : subd10_4 [-1, 1, 0] = true := by decide +kernel
theorem subd10_4_54 : subd10_4 [-1, 1, 1] = true := by decide +kernel
theorem subd10_4_55 : subd10_4 [-1, 1, 2] = true := by decide +kernel
theorem subd10_4_56 : subd10_4 [-1, 1, 3] = true := by decide +kernel
theorem subd10_4_57 : subd10_4 [-1, 1, 4] = true := by decide +kernel
theorem subd10_4_58 : subd10_4 [-1, 1, 5] = true := by decide +kernel
theorem subd10_4_59 : subd10_4 [-1, 1, 6] = true := by decide +kernel
theorem subd10_4_60 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_61 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_62 : subd10_4 [0, -4] = true := by decide +kernel
theorem subd10_4_63 : subd10_4 [0, -3] = true := by decide +kernel
theorem sbd10_4_1 : ∀ q ∈ blkd10_4_1, subd10_4 q = true := by
  unfold blkd10_4_1
  exact List.forall_mem_cons.2 ⟨subd10_4_32, List.forall_mem_cons.2 ⟨subd10_4_33, List.forall_mem_cons.2 ⟨subd10_4_34, List.forall_mem_cons.2 ⟨subd10_4_35, List.forall_mem_cons.2 ⟨subd10_4_36, List.forall_mem_cons.2 ⟨subd10_4_37, List.forall_mem_cons.2 ⟨subd10_4_38, List.forall_mem_cons.2 ⟨subd10_4_39, List.forall_mem_cons.2 ⟨subd10_4_40, List.forall_mem_cons.2 ⟨subd10_4_41, List.forall_mem_cons.2 ⟨subd10_4_42, List.forall_mem_cons.2 ⟨subd10_4_43, List.forall_mem_cons.2 ⟨subd10_4_44, List.forall_mem_cons.2 ⟨subd10_4_45, List.forall_mem_cons.2 ⟨subd10_4_46, List.forall_mem_cons.2 ⟨subd10_4_47, List.forall_mem_cons.2 ⟨subd10_4_48, List.forall_mem_cons.2 ⟨subd10_4_49, List.forall_mem_cons.2 ⟨subd10_4_50, List.forall_mem_cons.2 ⟨subd10_4_51, List.forall_mem_cons.2 ⟨subd10_4_52, List.forall_mem_cons.2 ⟨subd10_4_53, List.forall_mem_cons.2 ⟨subd10_4_54, List.forall_mem_cons.2 ⟨subd10_4_55, List.forall_mem_cons.2 ⟨subd10_4_56, List.forall_mem_cons.2 ⟨subd10_4_57, List.forall_mem_cons.2 ⟨subd10_4_58, List.forall_mem_cons.2 ⟨subd10_4_59, List.forall_mem_cons.2 ⟨subd10_4_60, List.forall_mem_cons.2 ⟨subd10_4_61, List.forall_mem_cons.2 ⟨subd10_4_62, List.forall_mem_cons.2 ⟨subd10_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_4_64 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_65 : subd10_4 [0, -1, -7] = true := by decide +kernel
theorem subd10_4_66 : subd10_4 [0, -1, -6] = true := by decide +kernel
theorem subd10_4_67 : subd10_4 [0, -1, -5] = true := by decide +kernel
theorem subd10_4_68 : subd10_4 [0, -1, -4] = true := by decide +kernel
theorem subd10_4_69 : subd10_4 [0, -1, -3] = true := by decide +kernel
theorem subd10_4_70 : subd10_4 [0, -1, -2] = true := by decide +kernel
theorem subd10_4_71 : subd10_4 [0, -1, -1] = true := by decide +kernel
theorem subd10_4_72 : subd10_4 [0, -1, 0] = true := by decide +kernel
theorem subd10_4_73 : subd10_4 [0, -1, 1] = true := by decide +kernel
theorem subd10_4_74 : subd10_4 [0, -1, 2] = true := by decide +kernel
theorem subd10_4_75 : subd10_4 [0, -1, 3] = true := by decide +kernel
theorem subd10_4_76 : subd10_4 [0, -1, 4] = true := by decide +kernel
theorem subd10_4_77 : subd10_4 [0, -1, 5] = true := by decide +kernel
theorem subd10_4_78 : subd10_4 [0, -1, 6] = true := by decide +kernel
theorem subd10_4_79 : subd10_4 [0, 0, -8] = true := by decide +kernel
theorem subd10_4_80 : subd10_4 [0, 0, -7] = true := by decide +kernel
theorem subd10_4_81 : subd10_4 [0, 0, -6] = true := by decide +kernel
theorem subd10_4_82 : subd10_4 [0, 0, -5] = true := by decide +kernel
theorem subd10_4_83 : subd10_4 [0, 0, -4] = true := by decide +kernel
theorem subd10_4_84 : subd10_4 [0, 0, -3] = true := by decide +kernel
theorem subd10_4_85 : subd10_4 [0, 0, -2] = true := by decide +kernel
theorem subd10_4_86 : subd10_4 [0, 0, -1] = true := by decide +kernel
theorem subd10_4_87 : subd10_4 [0, 0, 0] = true := by decide +kernel
theorem subd10_4_88 : subd10_4 [0, 0, 1] = true := by decide +kernel
theorem subd10_4_89 : subd10_4 [0, 0, 2] = true := by decide +kernel
theorem subd10_4_90 : subd10_4 [0, 0, 3] = true := by decide +kernel
theorem subd10_4_91 : subd10_4 [0, 0, 4] = true := by decide +kernel
theorem subd10_4_92 : subd10_4 [0, 0, 5] = true := by decide +kernel
theorem subd10_4_93 : subd10_4 [0, 0, 6] = true := by decide +kernel
theorem subd10_4_94 : subd10_4 [0, 0, 7] = true := by decide +kernel
theorem subd10_4_95 : subd10_4 [0, 1, -7] = true := by decide +kernel
theorem sbd10_4_2 : ∀ q ∈ blkd10_4_2, subd10_4 q = true := by
  unfold blkd10_4_2
  exact List.forall_mem_cons.2 ⟨subd10_4_64, List.forall_mem_cons.2 ⟨subd10_4_65, List.forall_mem_cons.2 ⟨subd10_4_66, List.forall_mem_cons.2 ⟨subd10_4_67, List.forall_mem_cons.2 ⟨subd10_4_68, List.forall_mem_cons.2 ⟨subd10_4_69, List.forall_mem_cons.2 ⟨subd10_4_70, List.forall_mem_cons.2 ⟨subd10_4_71, List.forall_mem_cons.2 ⟨subd10_4_72, List.forall_mem_cons.2 ⟨subd10_4_73, List.forall_mem_cons.2 ⟨subd10_4_74, List.forall_mem_cons.2 ⟨subd10_4_75, List.forall_mem_cons.2 ⟨subd10_4_76, List.forall_mem_cons.2 ⟨subd10_4_77, List.forall_mem_cons.2 ⟨subd10_4_78, List.forall_mem_cons.2 ⟨subd10_4_79, List.forall_mem_cons.2 ⟨subd10_4_80, List.forall_mem_cons.2 ⟨subd10_4_81, List.forall_mem_cons.2 ⟨subd10_4_82, List.forall_mem_cons.2 ⟨subd10_4_83, List.forall_mem_cons.2 ⟨subd10_4_84, List.forall_mem_cons.2 ⟨subd10_4_85, List.forall_mem_cons.2 ⟨subd10_4_86, List.forall_mem_cons.2 ⟨subd10_4_87, List.forall_mem_cons.2 ⟨subd10_4_88, List.forall_mem_cons.2 ⟨subd10_4_89, List.forall_mem_cons.2 ⟨subd10_4_90, List.forall_mem_cons.2 ⟨subd10_4_91, List.forall_mem_cons.2 ⟨subd10_4_92, List.forall_mem_cons.2 ⟨subd10_4_93, List.forall_mem_cons.2 ⟨subd10_4_94, List.forall_mem_cons.2 ⟨subd10_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
