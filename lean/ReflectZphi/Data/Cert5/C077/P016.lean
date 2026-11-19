import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_0 : subd10_1 [-7] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-6, -4] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-6, -3] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-6, -2] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [-6, -1] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [-6, 0] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [-6, 1] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [-6, 2] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [-6, 3] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [-6, 4] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [-6, 5] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [-6, 6] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [-5, -5] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [-5, -4] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [-5, -3] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [-5, -2] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [-5, -1] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [-5, 0] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [-5, 1] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [-5, 2] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [-5, 3] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [-5, 4] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [-5, 5] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [-5, 6] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [-5, 7] = true := by decide +kernel
theorem subd10_1_25 : subd10_1 [-4, -6] = true := by decide +kernel
theorem subd10_1_26 : subd10_1 [-4, -5] = true := by decide +kernel
theorem subd10_1_27 : subd10_1 [-4, -4] = true := by decide +kernel
theorem subd10_1_28 : subd10_1 [-4, -3] = true := by decide +kernel
theorem subd10_1_29 : subd10_1 [-4, -2] = true := by decide +kernel
theorem subd10_1_30 : subd10_1 [-4, -1] = true := by decide +kernel
theorem subd10_1_31 : subd10_1 [-4, 0] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_cons.2 ⟨subd10_1_25, List.forall_mem_cons.2 ⟨subd10_1_26, List.forall_mem_cons.2 ⟨subd10_1_27, List.forall_mem_cons.2 ⟨subd10_1_28, List.forall_mem_cons.2 ⟨subd10_1_29, List.forall_mem_cons.2 ⟨subd10_1_30, List.forall_mem_cons.2 ⟨subd10_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_32 : subd10_1 [-4, 1] = true := by decide +kernel
theorem subd10_1_33 : subd10_1 [-4, 2] = true := by decide +kernel
theorem subd10_1_34 : subd10_1 [-4, 3] = true := by decide +kernel
theorem subd10_1_35 : subd10_1 [-4, 4] = true := by decide +kernel
theorem subd10_1_36 : subd10_1 [-4, 5] = true := by decide +kernel
theorem subd10_1_37 : subd10_1 [-4, 6] = true := by decide +kernel
theorem subd10_1_38 : subd10_1 [-4, 7] = true := by decide +kernel
theorem subd10_1_39 : subd10_1 [-3, -7] = true := by decide +kernel
theorem subd10_1_40 : subd10_1 [-3, -6] = true := by decide +kernel
theorem subd10_1_41 : subd10_1 [-3, -5] = true := by decide +kernel
theorem subd10_1_42 : subd10_1 [-3, -4] = true := by decide +kernel
theorem subd10_1_43 : subd10_1 [-3, -3] = true := by decide +kernel
theorem subd10_1_44 : subd10_1 [-3, -2] = true := by decide +kernel
theorem subd10_1_45 : subd10_1 [-3, -1] = true := by decide +kernel
theorem subd10_1_46 : subd10_1 [-3, 0] = true := by decide +kernel
theorem subd10_1_47 : subd10_1 [-3, 1] = true := by decide +kernel
theorem subd10_1_48 : subd10_1 [-3, 2] = true := by decide +kernel
theorem subd10_1_49 : subd10_1 [-3, 3] = true := by decide +kernel
theorem subd10_1_50 : subd10_1 [-3, 4] = true := by decide +kernel
theorem subd10_1_51 : subd10_1 [-3, 5] = true := by decide +kernel
theorem subd10_1_52 : subd10_1 [-3, 6] = true := by decide +kernel
theorem subd10_1_53 : subd10_1 [-3, 7] = true := by decide +kernel
theorem subd10_1_54 : subd10_1 [-3, 8] = true := by decide +kernel
theorem subd10_1_55 : subd10_1 [-2, -8] = true := by decide +kernel
theorem subd10_1_56 : subd10_1 [-2, -7] = true := by decide +kernel
theorem subd10_1_57 : subd10_1 [-2, -6] = true := by decide +kernel
theorem subd10_1_58 : subd10_1 [-2, -5] = true := by decide +kernel
theorem subd10_1_59 : subd10_1 [-2, -4] = true := by decide +kernel
theorem subd10_1_60 : subd10_1 [-2, -3] = true := by decide +kernel
theorem subd10_1_61 : subd10_1 [-2, -2] = true := by decide +kernel
theorem subd10_1_62 : subd10_1 [-2, -1] = true := by decide +kernel
theorem subd10_1_63 : subd10_1 [-2, 0] = true := by decide +kernel
theorem sbd10_1_1 : ∀ q ∈ blkd10_1_1, subd10_1 q = true := by
  unfold blkd10_1_1
  exact List.forall_mem_cons.2 ⟨subd10_1_32, List.forall_mem_cons.2 ⟨subd10_1_33, List.forall_mem_cons.2 ⟨subd10_1_34, List.forall_mem_cons.2 ⟨subd10_1_35, List.forall_mem_cons.2 ⟨subd10_1_36, List.forall_mem_cons.2 ⟨subd10_1_37, List.forall_mem_cons.2 ⟨subd10_1_38, List.forall_mem_cons.2 ⟨subd10_1_39, List.forall_mem_cons.2 ⟨subd10_1_40, List.forall_mem_cons.2 ⟨subd10_1_41, List.forall_mem_cons.2 ⟨subd10_1_42, List.forall_mem_cons.2 ⟨subd10_1_43, List.forall_mem_cons.2 ⟨subd10_1_44, List.forall_mem_cons.2 ⟨subd10_1_45, List.forall_mem_cons.2 ⟨subd10_1_46, List.forall_mem_cons.2 ⟨subd10_1_47, List.forall_mem_cons.2 ⟨subd10_1_48, List.forall_mem_cons.2 ⟨subd10_1_49, List.forall_mem_cons.2 ⟨subd10_1_50, List.forall_mem_cons.2 ⟨subd10_1_51, List.forall_mem_cons.2 ⟨subd10_1_52, List.forall_mem_cons.2 ⟨subd10_1_53, List.forall_mem_cons.2 ⟨subd10_1_54, List.forall_mem_cons.2 ⟨subd10_1_55, List.forall_mem_cons.2 ⟨subd10_1_56, List.forall_mem_cons.2 ⟨subd10_1_57, List.forall_mem_cons.2 ⟨subd10_1_58, List.forall_mem_cons.2 ⟨subd10_1_59, List.forall_mem_cons.2 ⟨subd10_1_60, List.forall_mem_cons.2 ⟨subd10_1_61, List.forall_mem_cons.2 ⟨subd10_1_62, List.forall_mem_cons.2 ⟨subd10_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_64 : subd10_1 [-2, 1] = true := by decide +kernel
theorem subd10_1_65 : subd10_1 [-2, 2] = true := by decide +kernel
theorem subd10_1_66 : subd10_1 [-2, 3] = true := by decide +kernel
theorem subd10_1_67 : subd10_1 [-2, 4] = true := by decide +kernel
theorem subd10_1_68 : subd10_1 [-2, 5] = true := by decide +kernel
theorem subd10_1_69 : subd10_1 [-2, 6] = true := by decide +kernel
theorem subd10_1_70 : subd10_1 [-2, 7] = true := by decide +kernel
theorem subd10_1_71 : subd10_1 [-2, 8] = true := by decide +kernel
theorem subd10_1_72 : subd10_1 [-1, -8] = true := by decide +kernel
theorem subd10_1_73 : subd10_1 [-1, -7] = true := by decide +kernel
theorem subd10_1_74 : subd10_1 [-1, -6] = true := by decide +kernel
theorem subd10_1_75 : subd10_1 [-1, -5] = true := by decide +kernel
theorem subd10_1_76 : subd10_1 [-1, -4] = true := by decide +kernel
theorem subd10_1_77 : subd10_1 [-1, -3] = true := by decide +kernel
theorem subd10_1_78 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_79 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_80 : subd10_1 [-1, 0, -7] = true := by decide +kernel
theorem subd10_1_81 : subd10_1 [-1, 0, -6] = true := by decide +kernel
theorem subd10_1_82 : subd10_1 [-1, 0, -5] = true := by decide +kernel
theorem subd10_1_83 : subd10_1 [-1, 0, -4] = true := by decide +kernel
theorem subd10_1_84 : subd10_1 [-1, 0, -3] = true := by decide +kernel
theorem subd10_1_85 : subd10_1 [-1, 0, -2] = true := by decide +kernel
theorem subd10_1_86 : subd10_1 [-1, 0, -1] = true := by decide +kernel
theorem subd10_1_87 : subd10_1 [-1, 0, 0] = true := by decide +kernel
theorem subd10_1_88 : subd10_1 [-1, 0, 1] = true := by decide +kernel
theorem subd10_1_89 : subd10_1 [-1, 0, 2] = true := by decide +kernel
theorem subd10_1_90 : subd10_1 [-1, 0, 3] = true := by decide +kernel
theorem subd10_1_91 : subd10_1 [-1, 0, 4] = true := by decide +kernel
theorem subd10_1_92 : subd10_1 [-1, 0, 5] = true := by decide +kernel
theorem subd10_1_93 : subd10_1 [-1, 0, 6] = true := by decide +kernel
theorem subd10_1_94 : subd10_1 [-1, 1, -6] = true := by decide +kernel
theorem subd10_1_95 : subd10_1 [-1, 1, -5] = true := by decide +kernel
theorem sbd10_1_2 : ∀ q ∈ blkd10_1_2, subd10_1 q = true := by
  unfold blkd10_1_2
  exact List.forall_mem_cons.2 ⟨subd10_1_64, List.forall_mem_cons.2 ⟨subd10_1_65, List.forall_mem_cons.2 ⟨subd10_1_66, List.forall_mem_cons.2 ⟨subd10_1_67, List.forall_mem_cons.2 ⟨subd10_1_68, List.forall_mem_cons.2 ⟨subd10_1_69, List.forall_mem_cons.2 ⟨subd10_1_70, List.forall_mem_cons.2 ⟨subd10_1_71, List.forall_mem_cons.2 ⟨subd10_1_72, List.forall_mem_cons.2 ⟨subd10_1_73, List.forall_mem_cons.2 ⟨subd10_1_74, List.forall_mem_cons.2 ⟨subd10_1_75, List.forall_mem_cons.2 ⟨subd10_1_76, List.forall_mem_cons.2 ⟨subd10_1_77, List.forall_mem_cons.2 ⟨subd10_1_78, List.forall_mem_cons.2 ⟨subd10_1_79, List.forall_mem_cons.2 ⟨subd10_1_80, List.forall_mem_cons.2 ⟨subd10_1_81, List.forall_mem_cons.2 ⟨subd10_1_82, List.forall_mem_cons.2 ⟨subd10_1_83, List.forall_mem_cons.2 ⟨subd10_1_84, List.forall_mem_cons.2 ⟨subd10_1_85, List.forall_mem_cons.2 ⟨subd10_1_86, List.forall_mem_cons.2 ⟨subd10_1_87, List.forall_mem_cons.2 ⟨subd10_1_88, List.forall_mem_cons.2 ⟨subd10_1_89, List.forall_mem_cons.2 ⟨subd10_1_90, List.forall_mem_cons.2 ⟨subd10_1_91, List.forall_mem_cons.2 ⟨subd10_1_92, List.forall_mem_cons.2 ⟨subd10_1_93, List.forall_mem_cons.2 ⟨subd10_1_94, List.forall_mem_cons.2 ⟨subd10_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
