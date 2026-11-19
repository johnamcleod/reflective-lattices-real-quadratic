import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_0 : subd10_2 [-5] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-4, -3] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-4, -2] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-4, -1] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-4, 0] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-4, 1] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-4, 2] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-4, 3] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-4, 4] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-3, -4] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-3, -3] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-3, -2] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [-3, -1] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [-3, 0] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [-3, 1] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [-3, 2] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [-3, 3] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [-3, 4] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [-2, -5] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [-2, -4] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [-2, -3] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [-2, -2] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [-2, -1] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [-2, 0] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [-2, 1] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [-2, 2] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [-2, 3] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [-2, 4] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [-2, 5] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [-1, -5] = true := by decide +kernel
theorem subd10_2_30 : subd10_2 [-1, -4] = true := by decide +kernel
theorem subd10_2_31 : subd10_2 [-1, -3] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_cons.2 ⟨subd10_2_30, List.forall_mem_cons.2 ⟨subd10_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_32 : subd10_2 [-1, -2] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-1, -1] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-1, 0] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-1, 1] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-1, 2] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-1, 3] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-1, 4] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-1, 5] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [0, -6] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [0, -5] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [0, -4] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [0, 3] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [0, 4] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [0, 5] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [1, -6] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [1, -5] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [1, -4] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [1, -3] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [1, -2] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [1, -1] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [1, 0] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [1, 1] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [1, 2] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [1, 3] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [1, 4] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [2, -6] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [2, -5] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [2, -4] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [2, -3] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [2, -2] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [2, -1] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [2, 0] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [2, 1] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [2, 2] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [2, 3] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [2, 4] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [3, -5] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [3, -4] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [3, -3] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [3, -2] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [3, -1] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [3, 0] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [3, 1] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [3, 2] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [3, 3] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [4, -5] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [4, -4] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [4, -3] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [4, -2] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [4, -1] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [4, 0] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [4, 1] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [4, 2] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [5] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-4] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-3, -3] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-3, -2] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-3, -1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-3, 0] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-3, 1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-3, 2] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-3, 3] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-3, 4] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-2, -4] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-2, -1] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-2, 0] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-2, 1] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-2, 2] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-2, 3] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-2, 4] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-1, -5] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-1, -4] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [-1, 3] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [-1, 4] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [0, -5] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [0, -4] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [0, -2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
