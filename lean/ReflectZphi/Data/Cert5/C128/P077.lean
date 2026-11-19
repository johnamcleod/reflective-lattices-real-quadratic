import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-4] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [-3, -6] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [-3, -5] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [-3, -4] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [-3, -3] = true := by decide +kernel
theorem subd10_5_5 : subd10_5 [-3, -2] = true := by decide +kernel
theorem subd10_5_6 : subd10_5 [-3, -1] = true := by decide +kernel
theorem subd10_5_7 : subd10_5 [-3, 0] = true := by decide +kernel
theorem subd10_5_8 : subd10_5 [-3, 1] = true := by decide +kernel
theorem subd10_5_9 : subd10_5 [-3, 2] = true := by decide +kernel
theorem subd10_5_10 : subd10_5 [-2, -6] = true := by decide +kernel
theorem subd10_5_11 : subd10_5 [-2, -5] = true := by decide +kernel
theorem subd10_5_12 : subd10_5 [-2, -4] = true := by decide +kernel
theorem subd10_5_13 : subd10_5 [-2, -3] = true := by decide +kernel
theorem subd10_5_14 : subd10_5 [-2, -2] = true := by decide +kernel
theorem subd10_5_15 : subd10_5 [-2, -1] = true := by decide +kernel
theorem subd10_5_16 : subd10_5 [-2, 0] = true := by decide +kernel
theorem subd10_5_17 : subd10_5 [-2, 1] = true := by decide +kernel
theorem subd10_5_18 : subd10_5 [-2, 2] = true := by decide +kernel
theorem subd10_5_19 : subd10_5 [-2, 3] = true := by decide +kernel
theorem subd10_5_20 : subd10_5 [-1, -6] = true := by decide +kernel
theorem subd10_5_21 : subd10_5 [-1, -5] = true := by decide +kernel
theorem subd10_5_22 : subd10_5 [-1, -4] = true := by decide +kernel
theorem subd10_5_23 : subd10_5 [-1, -3] = true := by decide +kernel
theorem subd10_5_24 : subd10_5 [-1, -2] = true := by decide +kernel
theorem subd10_5_25 : subd10_5 [-1, -1] = true := by decide +kernel
theorem subd10_5_26 : subd10_5 [-1, 0] = true := by decide +kernel
theorem subd10_5_27 : subd10_5 [-1, 1] = true := by decide +kernel
theorem subd10_5_28 : subd10_5 [-1, 2] = true := by decide +kernel
theorem subd10_5_29 : subd10_5 [-1, 3] = true := by decide +kernel
theorem subd10_5_30 : subd10_5 [-1, 4] = true := by decide +kernel
theorem subd10_5_31 : subd10_5 [0, -6] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_cons.2 ⟨subd10_5_5, List.forall_mem_cons.2 ⟨subd10_5_6, List.forall_mem_cons.2 ⟨subd10_5_7, List.forall_mem_cons.2 ⟨subd10_5_8, List.forall_mem_cons.2 ⟨subd10_5_9, List.forall_mem_cons.2 ⟨subd10_5_10, List.forall_mem_cons.2 ⟨subd10_5_11, List.forall_mem_cons.2 ⟨subd10_5_12, List.forall_mem_cons.2 ⟨subd10_5_13, List.forall_mem_cons.2 ⟨subd10_5_14, List.forall_mem_cons.2 ⟨subd10_5_15, List.forall_mem_cons.2 ⟨subd10_5_16, List.forall_mem_cons.2 ⟨subd10_5_17, List.forall_mem_cons.2 ⟨subd10_5_18, List.forall_mem_cons.2 ⟨subd10_5_19, List.forall_mem_cons.2 ⟨subd10_5_20, List.forall_mem_cons.2 ⟨subd10_5_21, List.forall_mem_cons.2 ⟨subd10_5_22, List.forall_mem_cons.2 ⟨subd10_5_23, List.forall_mem_cons.2 ⟨subd10_5_24, List.forall_mem_cons.2 ⟨subd10_5_25, List.forall_mem_cons.2 ⟨subd10_5_26, List.forall_mem_cons.2 ⟨subd10_5_27, List.forall_mem_cons.2 ⟨subd10_5_28, List.forall_mem_cons.2 ⟨subd10_5_29, List.forall_mem_cons.2 ⟨subd10_5_30, List.forall_mem_cons.2 ⟨subd10_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_32 : subd10_5 [0, -5] = true := by decide +kernel
theorem subd10_5_33 : subd10_5 [0, -4] = true := by decide +kernel
theorem subd10_5_34 : subd10_5 [0, -3] = true := by decide +kernel
theorem subd10_5_35 : subd10_5 [0, -2] = true := by decide +kernel
theorem subd10_5_36 : subd10_5 [0, -1] = true := by decide +kernel
theorem subd10_5_37 : subd10_5 [0, 0] = true := by decide +kernel
theorem subd10_5_38 : subd10_5 [0, 1] = true := by decide +kernel
theorem subd10_5_39 : subd10_5 [0, 2] = true := by decide +kernel
theorem subd10_5_40 : subd10_5 [0, 3] = true := by decide +kernel
theorem subd10_5_41 : subd10_5 [0, 4] = true := by decide +kernel
theorem subd10_5_42 : subd10_5 [0, 5] = true := by decide +kernel
theorem subd10_5_43 : subd10_5 [1, -5] = true := by decide +kernel
theorem subd10_5_44 : subd10_5 [1, -4] = true := by decide +kernel
theorem subd10_5_45 : subd10_5 [1, -3] = true := by decide +kernel
theorem subd10_5_46 : subd10_5 [1, -2] = true := by decide +kernel
theorem subd10_5_47 : subd10_5 [1, -1] = true := by decide +kernel
theorem subd10_5_48 : subd10_5 [1, 0] = true := by decide +kernel
theorem subd10_5_49 : subd10_5 [1, 1] = true := by decide +kernel
theorem subd10_5_50 : subd10_5 [1, 2] = true := by decide +kernel
theorem subd10_5_51 : subd10_5 [1, 3] = true := by decide +kernel
theorem subd10_5_52 : subd10_5 [1, 4] = true := by decide +kernel
theorem subd10_5_53 : subd10_5 [1, 5] = true := by decide +kernel
theorem subd10_5_54 : subd10_5 [2, -4] = true := by decide +kernel
theorem subd10_5_55 : subd10_5 [2, -3] = true := by decide +kernel
theorem subd10_5_56 : subd10_5 [2, -2] = true := by decide +kernel
theorem subd10_5_57 : subd10_5 [2, -1] = true := by decide +kernel
theorem subd10_5_58 : subd10_5 [2, 0] = true := by decide +kernel
theorem subd10_5_59 : subd10_5 [2, 1] = true := by decide +kernel
theorem subd10_5_60 : subd10_5 [2, 2] = true := by decide +kernel
theorem subd10_5_61 : subd10_5 [2, 3] = true := by decide +kernel
theorem subd10_5_62 : subd10_5 [2, 4] = true := by decide +kernel
theorem subd10_5_63 : subd10_5 [2, 5] = true := by decide +kernel
theorem sbd10_5_1 : ∀ q ∈ blkd10_5_1, subd10_5 q = true := by
  unfold blkd10_5_1
  exact List.forall_mem_cons.2 ⟨subd10_5_32, List.forall_mem_cons.2 ⟨subd10_5_33, List.forall_mem_cons.2 ⟨subd10_5_34, List.forall_mem_cons.2 ⟨subd10_5_35, List.forall_mem_cons.2 ⟨subd10_5_36, List.forall_mem_cons.2 ⟨subd10_5_37, List.forall_mem_cons.2 ⟨subd10_5_38, List.forall_mem_cons.2 ⟨subd10_5_39, List.forall_mem_cons.2 ⟨subd10_5_40, List.forall_mem_cons.2 ⟨subd10_5_41, List.forall_mem_cons.2 ⟨subd10_5_42, List.forall_mem_cons.2 ⟨subd10_5_43, List.forall_mem_cons.2 ⟨subd10_5_44, List.forall_mem_cons.2 ⟨subd10_5_45, List.forall_mem_cons.2 ⟨subd10_5_46, List.forall_mem_cons.2 ⟨subd10_5_47, List.forall_mem_cons.2 ⟨subd10_5_48, List.forall_mem_cons.2 ⟨subd10_5_49, List.forall_mem_cons.2 ⟨subd10_5_50, List.forall_mem_cons.2 ⟨subd10_5_51, List.forall_mem_cons.2 ⟨subd10_5_52, List.forall_mem_cons.2 ⟨subd10_5_53, List.forall_mem_cons.2 ⟨subd10_5_54, List.forall_mem_cons.2 ⟨subd10_5_55, List.forall_mem_cons.2 ⟨subd10_5_56, List.forall_mem_cons.2 ⟨subd10_5_57, List.forall_mem_cons.2 ⟨subd10_5_58, List.forall_mem_cons.2 ⟨subd10_5_59, List.forall_mem_cons.2 ⟨subd10_5_60, List.forall_mem_cons.2 ⟨subd10_5_61, List.forall_mem_cons.2 ⟨subd10_5_62, List.forall_mem_cons.2 ⟨subd10_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_5_64 : subd10_5 [3, -3] = true := by decide +kernel
theorem subd10_5_65 : subd10_5 [3, -2] = true := by decide +kernel
theorem subd10_5_66 : subd10_5 [3, -1] = true := by decide +kernel
theorem subd10_5_67 : subd10_5 [3, 0] = true := by decide +kernel
theorem subd10_5_68 : subd10_5 [3, 1] = true := by decide +kernel
theorem subd10_5_69 : subd10_5 [3, 2] = true := by decide +kernel
theorem subd10_5_70 : subd10_5 [3, 3] = true := by decide +kernel
theorem subd10_5_71 : subd10_5 [3, 4] = true := by decide +kernel
theorem subd10_5_72 : subd10_5 [3, 5] = true := by decide +kernel
theorem subd10_5_73 : subd10_5 [4] = true := by decide +kernel
theorem sbd10_5_2 : ∀ q ∈ blkd10_5_2, subd10_5 q = true := by
  unfold blkd10_5_2
  exact List.forall_mem_cons.2 ⟨subd10_5_64, List.forall_mem_cons.2 ⟨subd10_5_65, List.forall_mem_cons.2 ⟨subd10_5_66, List.forall_mem_cons.2 ⟨subd10_5_67, List.forall_mem_cons.2 ⟨subd10_5_68, List.forall_mem_cons.2 ⟨subd10_5_69, List.forall_mem_cons.2 ⟨subd10_5_70, List.forall_mem_cons.2 ⟨subd10_5_71, List.forall_mem_cons.2 ⟨subd10_5_72, List.forall_mem_cons.2 ⟨subd10_5_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-3, -2] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-3, -1] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [-3, 0] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [-3, 1] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [-3, 2] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [-2, -3] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [-2, -2] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [-2, -1] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [-2, 0, -7] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [-2, 0, -6] = true := by decide +kernel
theorem subd10_6_10 : subd10_6 [-2, 0, -5] = true := by decide +kernel
theorem subd10_6_11 : subd10_6 [-2, 0, -4] = true := by decide +kernel
theorem subd10_6_12 : subd10_6 [-2, 0, -3] = true := by decide +kernel
theorem subd10_6_13 : subd10_6 [-2, 0, -2] = true := by decide +kernel
theorem subd10_6_14 : subd10_6 [-2, 0, -1] = true := by decide +kernel
theorem subd10_6_15 : subd10_6 [-2, 0, 0] = true := by decide +kernel
theorem subd10_6_16 : subd10_6 [-2, 0, 1] = true := by decide +kernel
theorem subd10_6_17 : subd10_6 [-2, 0, 2] = true := by decide +kernel
theorem subd10_6_18 : subd10_6 [-2, 0, 3] = true := by decide +kernel
theorem subd10_6_19 : subd10_6 [-2, 0, 4] = true := by decide +kernel
theorem subd10_6_20 : subd10_6 [-2, 0, 5] = true := by decide +kernel
theorem subd10_6_21 : subd10_6 [-2, 0, 6] = true := by decide +kernel
theorem subd10_6_22 : subd10_6 [-2, 0, 7] = true := by decide +kernel
theorem subd10_6_23 : subd10_6 [-2, 1, -8] = true := by decide +kernel
theorem subd10_6_24 : subd10_6 [-2, 1, -7] = true := by decide +kernel
theorem subd10_6_25 : subd10_6 [-2, 1, -6] = true := by decide +kernel
theorem subd10_6_26 : subd10_6 [-2, 1, -5] = true := by decide +kernel
theorem subd10_6_27 : subd10_6 [-2, 1, -4] = true := by decide +kernel
theorem subd10_6_28 : subd10_6 [-2, 1, -3] = true := by decide +kernel
theorem subd10_6_29 : subd10_6 [-2, 1, -2] = true := by decide +kernel
theorem subd10_6_30 : subd10_6 [-2, 1, -1] = true := by decide +kernel
theorem subd10_6_31 : subd10_6 [-2, 1, 0] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_cons.2 ⟨subd10_6_10, List.forall_mem_cons.2 ⟨subd10_6_11, List.forall_mem_cons.2 ⟨subd10_6_12, List.forall_mem_cons.2 ⟨subd10_6_13, List.forall_mem_cons.2 ⟨subd10_6_14, List.forall_mem_cons.2 ⟨subd10_6_15, List.forall_mem_cons.2 ⟨subd10_6_16, List.forall_mem_cons.2 ⟨subd10_6_17, List.forall_mem_cons.2 ⟨subd10_6_18, List.forall_mem_cons.2 ⟨subd10_6_19, List.forall_mem_cons.2 ⟨subd10_6_20, List.forall_mem_cons.2 ⟨subd10_6_21, List.forall_mem_cons.2 ⟨subd10_6_22, List.forall_mem_cons.2 ⟨subd10_6_23, List.forall_mem_cons.2 ⟨subd10_6_24, List.forall_mem_cons.2 ⟨subd10_6_25, List.forall_mem_cons.2 ⟨subd10_6_26, List.forall_mem_cons.2 ⟨subd10_6_27, List.forall_mem_cons.2 ⟨subd10_6_28, List.forall_mem_cons.2 ⟨subd10_6_29, List.forall_mem_cons.2 ⟨subd10_6_30, List.forall_mem_cons.2 ⟨subd10_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_32 : subd10_6 [-2, 1, 1] = true := by decide +kernel
theorem subd10_6_33 : subd10_6 [-2, 1, 2] = true := by decide +kernel
theorem subd10_6_34 : subd10_6 [-2, 1, 3] = true := by decide +kernel
theorem subd10_6_35 : subd10_6 [-2, 1, 4] = true := by decide +kernel
theorem subd10_6_36 : subd10_6 [-2, 1, 5] = true := by decide +kernel
theorem subd10_6_37 : subd10_6 [-2, 1, 6] = true := by decide +kernel
theorem subd10_6_38 : subd10_6 [-2, 1, 7] = true := by decide +kernel
theorem subd10_6_39 : subd10_6 [-2, 2] = true := by decide +kernel
theorem subd10_6_40 : subd10_6 [-2, 3] = true := by decide +kernel
theorem subd10_6_41 : subd10_6 [-1, -4] = true := by decide +kernel
theorem subd10_6_42 : subd10_6 [-1, -3] = true := by decide +kernel
theorem subd10_6_43 : subd10_6 [-1, -2, -7] = true := by decide +kernel
theorem subd10_6_44 : subd10_6 [-1, -2, -6] = true := by decide +kernel
theorem subd10_6_45 : subd10_6 [-1, -2, -5] = true := by decide +kernel
theorem subd10_6_46 : subd10_6 [-1, -2, -4] = true := by decide +kernel
theorem subd10_6_47 : subd10_6 [-1, -2, -3] = true := by decide +kernel
theorem subd10_6_48 : subd10_6 [-1, -2, -2] = true := by decide +kernel
theorem subd10_6_49 : subd10_6 [-1, -2, -1] = true := by decide +kernel
theorem subd10_6_50 : subd10_6 [-1, -2, 0] = true := by decide +kernel
theorem subd10_6_51 : subd10_6 [-1, -2, 1] = true := by decide +kernel
theorem subd10_6_52 : subd10_6 [-1, -2, 2] = true := by decide +kernel
theorem subd10_6_53 : subd10_6 [-1, -2, 3] = true := by decide +kernel
theorem subd10_6_54 : subd10_6 [-1, -2, 4] = true := by decide +kernel
theorem subd10_6_55 : subd10_6 [-1, -2, 5] = true := by decide +kernel
theorem subd10_6_56 : subd10_6 [-1, -2, 6] = true := by decide +kernel
theorem subd10_6_57 : subd10_6 [-1, -2, 7] = true := by decide +kernel
theorem subd10_6_58 : subd10_6 [-1, -1, -8] = true := by decide +kernel
theorem subd10_6_59 : subd10_6 [-1, -1, -7] = true := by decide +kernel
theorem subd10_6_60 : subd10_6 [-1, -1, -6] = true := by decide +kernel
theorem subd10_6_61 : subd10_6 [-1, -1, -5] = true := by decide +kernel
theorem subd10_6_62 : subd10_6 [-1, -1, -4] = true := by decide +kernel
theorem subd10_6_63 : subd10_6 [-1, -1, -3] = true := by decide +kernel
theorem sbd10_6_1 : ∀ q ∈ blkd10_6_1, subd10_6 q = true := by
  unfold blkd10_6_1
  exact List.forall_mem_cons.2 ⟨subd10_6_32, List.forall_mem_cons.2 ⟨subd10_6_33, List.forall_mem_cons.2 ⟨subd10_6_34, List.forall_mem_cons.2 ⟨subd10_6_35, List.forall_mem_cons.2 ⟨subd10_6_36, List.forall_mem_cons.2 ⟨subd10_6_37, List.forall_mem_cons.2 ⟨subd10_6_38, List.forall_mem_cons.2 ⟨subd10_6_39, List.forall_mem_cons.2 ⟨subd10_6_40, List.forall_mem_cons.2 ⟨subd10_6_41, List.forall_mem_cons.2 ⟨subd10_6_42, List.forall_mem_cons.2 ⟨subd10_6_43, List.forall_mem_cons.2 ⟨subd10_6_44, List.forall_mem_cons.2 ⟨subd10_6_45, List.forall_mem_cons.2 ⟨subd10_6_46, List.forall_mem_cons.2 ⟨subd10_6_47, List.forall_mem_cons.2 ⟨subd10_6_48, List.forall_mem_cons.2 ⟨subd10_6_49, List.forall_mem_cons.2 ⟨subd10_6_50, List.forall_mem_cons.2 ⟨subd10_6_51, List.forall_mem_cons.2 ⟨subd10_6_52, List.forall_mem_cons.2 ⟨subd10_6_53, List.forall_mem_cons.2 ⟨subd10_6_54, List.forall_mem_cons.2 ⟨subd10_6_55, List.forall_mem_cons.2 ⟨subd10_6_56, List.forall_mem_cons.2 ⟨subd10_6_57, List.forall_mem_cons.2 ⟨subd10_6_58, List.forall_mem_cons.2 ⟨subd10_6_59, List.forall_mem_cons.2 ⟨subd10_6_60, List.forall_mem_cons.2 ⟨subd10_6_61, List.forall_mem_cons.2 ⟨subd10_6_62, List.forall_mem_cons.2 ⟨subd10_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
