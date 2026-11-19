import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_0 : subd9_2 [-3] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-2, -3] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-2, -2] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-2, -1] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-2, 0] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-2, 1] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-2, 2] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-1, -3] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-1, -2] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-1, -1] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-1, 0] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-1, 1] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-1, 2] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-1, 3] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [0, -4] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [0, 3] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [1, -4] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [1, -3] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [1, -2] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [1, -1] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [1, 0] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [1, 1] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [1, 2] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [2, -2] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [2, -1] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_32 : subd9_2 [2, 0] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [2, 1] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [2, 2] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [3] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-5] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-4, -6] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-4, -5] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-4, -4] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-4, -3] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-4, -2] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-4, -1] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-4, 0] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-4, 1] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-3, -6] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-3, -5] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-3, -4] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-3, -3] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-3, -2] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-3, -1] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-3, 0] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-3, 1] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-3, 2] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-2, -6] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-2, -4] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-1, -6] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-1, -3] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [-1, 4] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [0, -5] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [1, 4] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [1, 5] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [2, -2] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [2, -1] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [2, 2] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [2, 3] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [2, 4] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [2, 5] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [3, -3] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [3, -2] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [3, -1] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [3, 0] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [3, 1] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [3, 2] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [3, 3] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [3, 4] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [3, 5] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [4, -2] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [4, -1] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [4, 0] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [4, 1] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [4, 2] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [4, 3] = true := by decide +kernel
theorem subd9_3_85 : subd9_3 [4, 4] = true := by decide +kernel
theorem subd9_3_86 : subd9_3 [4, 5] = true := by decide +kernel
theorem subd9_3_87 : subd9_3 [5] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_cons.2 ⟨subd9_3_85, List.forall_mem_cons.2 ⟨subd9_3_86, List.forall_mem_cons.2 ⟨subd9_3_87, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [0] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [1] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C136
