import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_6_0 : subd6_6 [-6] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-5, -5] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-5, -4] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-5, -3] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-5, -2] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-5, -1] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [-5, 0] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [-5, 1] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [-5, 2] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [-5, 3] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [-4, -6] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [-4, -5] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [-4, -4] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [-4, -3] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [-4, -2] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [-4, -1] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [-4, 0] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [-4, 1] = true := by decide +kernel
theorem subd6_6_18 : subd6_6 [-4, 2] = true := by decide +kernel
theorem subd6_6_19 : subd6_6 [-4, 3] = true := by decide +kernel
theorem subd6_6_20 : subd6_6 [-3, -6] = true := by decide +kernel
theorem subd6_6_21 : subd6_6 [-3, -5] = true := by decide +kernel
theorem subd6_6_22 : subd6_6 [-3, -4] = true := by decide +kernel
theorem subd6_6_23 : subd6_6 [-3, -3] = true := by decide +kernel
theorem subd6_6_24 : subd6_6 [-3, -2] = true := by decide +kernel
theorem subd6_6_25 : subd6_6 [-3, -1] = true := by decide +kernel
theorem subd6_6_26 : subd6_6 [-3, 0] = true := by decide +kernel
theorem subd6_6_27 : subd6_6 [-3, 1] = true := by decide +kernel
theorem subd6_6_28 : subd6_6 [-3, 2] = true := by decide +kernel
theorem subd6_6_29 : subd6_6 [-3, 3] = true := by decide +kernel
theorem subd6_6_30 : subd6_6 [-3, 4] = true := by decide +kernel
theorem subd6_6_31 : subd6_6 [-2, -6] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_cons.2 ⟨subd6_6_18, List.forall_mem_cons.2 ⟨subd6_6_19, List.forall_mem_cons.2 ⟨subd6_6_20, List.forall_mem_cons.2 ⟨subd6_6_21, List.forall_mem_cons.2 ⟨subd6_6_22, List.forall_mem_cons.2 ⟨subd6_6_23, List.forall_mem_cons.2 ⟨subd6_6_24, List.forall_mem_cons.2 ⟨subd6_6_25, List.forall_mem_cons.2 ⟨subd6_6_26, List.forall_mem_cons.2 ⟨subd6_6_27, List.forall_mem_cons.2 ⟨subd6_6_28, List.forall_mem_cons.2 ⟨subd6_6_29, List.forall_mem_cons.2 ⟨subd6_6_30, List.forall_mem_cons.2 ⟨subd6_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_32 : subd6_6 [-2, -5] = true := by decide +kernel
theorem subd6_6_33 : subd6_6 [-2, -4] = true := by decide +kernel
theorem subd6_6_34 : subd6_6 [-2, -3] = true := by decide +kernel
theorem subd6_6_35 : subd6_6 [-2, -2] = true := by decide +kernel
theorem subd6_6_36 : subd6_6 [-2, -1] = true := by decide +kernel
theorem subd6_6_37 : subd6_6 [-2, 0] = true := by decide +kernel
theorem subd6_6_38 : subd6_6 [-2, 1] = true := by decide +kernel
theorem subd6_6_39 : subd6_6 [-2, 2] = true := by decide +kernel
theorem subd6_6_40 : subd6_6 [-2, 3] = true := by decide +kernel
theorem subd6_6_41 : subd6_6 [-2, 4] = true := by decide +kernel
theorem subd6_6_42 : subd6_6 [-2, 5] = true := by decide +kernel
theorem subd6_6_43 : subd6_6 [-1, -6] = true := by decide +kernel
theorem subd6_6_44 : subd6_6 [-1, -5] = true := by decide +kernel
theorem subd6_6_45 : subd6_6 [-1, -4] = true := by decide +kernel
theorem subd6_6_46 : subd6_6 [-1, -3] = true := by decide +kernel
theorem subd6_6_47 : subd6_6 [-1, -2] = true := by decide +kernel
theorem subd6_6_48 : subd6_6 [-1, -1] = true := by decide +kernel
theorem subd6_6_49 : subd6_6 [-1, 0, -7] = true := by decide +kernel
theorem subd6_6_50 : subd6_6 [-1, 0, -6] = true := by decide +kernel
theorem subd6_6_51 : subd6_6 [-1, 0, -5] = true := by decide +kernel
theorem subd6_6_52 : subd6_6 [-1, 0, -4] = true := by decide +kernel
theorem subd6_6_53 : subd6_6 [-1, 0, -3] = true := by decide +kernel
theorem subd6_6_54 : subd6_6 [-1, 0, -2] = true := by decide +kernel
theorem subd6_6_55 : subd6_6 [-1, 0, -1] = true := by decide +kernel
theorem subd6_6_56 : subd6_6 [-1, 0, 0] = true := by decide +kernel
theorem subd6_6_57 : subd6_6 [-1, 0, 1] = true := by decide +kernel
theorem subd6_6_58 : subd6_6 [-1, 0, 2] = true := by decide +kernel
theorem subd6_6_59 : subd6_6 [-1, 0, 3] = true := by decide +kernel
theorem subd6_6_60 : subd6_6 [-1, 0, 4] = true := by decide +kernel
theorem subd6_6_61 : subd6_6 [-1, 0, 5] = true := by decide +kernel
theorem subd6_6_62 : subd6_6 [-1, 0, 6] = true := by decide +kernel
theorem subd6_6_63 : subd6_6 [-1, 1] = true := by decide +kernel
theorem sbd6_6_1 : ∀ q ∈ blkd6_6_1, subd6_6 q = true := by
  unfold blkd6_6_1
  exact List.forall_mem_cons.2 ⟨subd6_6_32, List.forall_mem_cons.2 ⟨subd6_6_33, List.forall_mem_cons.2 ⟨subd6_6_34, List.forall_mem_cons.2 ⟨subd6_6_35, List.forall_mem_cons.2 ⟨subd6_6_36, List.forall_mem_cons.2 ⟨subd6_6_37, List.forall_mem_cons.2 ⟨subd6_6_38, List.forall_mem_cons.2 ⟨subd6_6_39, List.forall_mem_cons.2 ⟨subd6_6_40, List.forall_mem_cons.2 ⟨subd6_6_41, List.forall_mem_cons.2 ⟨subd6_6_42, List.forall_mem_cons.2 ⟨subd6_6_43, List.forall_mem_cons.2 ⟨subd6_6_44, List.forall_mem_cons.2 ⟨subd6_6_45, List.forall_mem_cons.2 ⟨subd6_6_46, List.forall_mem_cons.2 ⟨subd6_6_47, List.forall_mem_cons.2 ⟨subd6_6_48, List.forall_mem_cons.2 ⟨subd6_6_49, List.forall_mem_cons.2 ⟨subd6_6_50, List.forall_mem_cons.2 ⟨subd6_6_51, List.forall_mem_cons.2 ⟨subd6_6_52, List.forall_mem_cons.2 ⟨subd6_6_53, List.forall_mem_cons.2 ⟨subd6_6_54, List.forall_mem_cons.2 ⟨subd6_6_55, List.forall_mem_cons.2 ⟨subd6_6_56, List.forall_mem_cons.2 ⟨subd6_6_57, List.forall_mem_cons.2 ⟨subd6_6_58, List.forall_mem_cons.2 ⟨subd6_6_59, List.forall_mem_cons.2 ⟨subd6_6_60, List.forall_mem_cons.2 ⟨subd6_6_61, List.forall_mem_cons.2 ⟨subd6_6_62, List.forall_mem_cons.2 ⟨subd6_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_64 : subd6_6 [-1, 2] = true := by decide +kernel
theorem subd6_6_65 : subd6_6 [-1, 3] = true := by decide +kernel
theorem subd6_6_66 : subd6_6 [-1, 4] = true := by decide +kernel
theorem subd6_6_67 : subd6_6 [-1, 5] = true := by decide +kernel
theorem subd6_6_68 : subd6_6 [0, -6] = true := by decide +kernel
theorem subd6_6_69 : subd6_6 [0, -5] = true := by decide +kernel
theorem subd6_6_70 : subd6_6 [0, -4] = true := by decide +kernel
theorem subd6_6_71 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_72 : subd6_6 [0, -2] = true := by decide +kernel
theorem subd6_6_73 : subd6_6 [0, -1] = true := by decide +kernel
theorem subd6_6_74 : subd6_6 [0, 0, -7] = true := by decide +kernel
theorem subd6_6_75 : subd6_6 [0, 0, -6] = true := by decide +kernel
theorem subd6_6_76 : subd6_6 [0, 0, -5] = true := by decide +kernel
theorem subd6_6_77 : subd6_6 [0, 0, -4] = true := by decide +kernel
theorem subd6_6_78 : subd6_6 [0, 0, -3] = true := by decide +kernel
theorem subd6_6_79 : subd6_6 [0, 0, -2] = true := by decide +kernel
theorem subd6_6_80 : subd6_6 [0, 0, -1] = true := by decide +kernel
theorem subd6_6_81 : subd6_6 [0, 0, 0] = true := by decide +kernel
theorem subd6_6_82 : subd6_6 [0, 0, 1] = true := by decide +kernel
theorem subd6_6_83 : subd6_6 [0, 0, 2] = true := by decide +kernel
theorem subd6_6_84 : subd6_6 [0, 0, 3] = true := by decide +kernel
theorem subd6_6_85 : subd6_6 [0, 0, 4] = true := by decide +kernel
theorem subd6_6_86 : subd6_6 [0, 0, 5] = true := by decide +kernel
theorem subd6_6_87 : subd6_6 [0, 0, 6] = true := by decide +kernel
theorem subd6_6_88 : subd6_6 [0, 1] = true := by decide +kernel
theorem subd6_6_89 : subd6_6 [0, 2] = true := by decide +kernel
theorem subd6_6_90 : subd6_6 [0, 3] = true := by decide +kernel
theorem subd6_6_91 : subd6_6 [0, 4] = true := by decide +kernel
theorem subd6_6_92 : subd6_6 [0, 5] = true := by decide +kernel
theorem subd6_6_93 : subd6_6 [1, -6] = true := by decide +kernel
theorem subd6_6_94 : subd6_6 [1, -5] = true := by decide +kernel
theorem subd6_6_95 : subd6_6 [1, -4] = true := by decide +kernel
theorem sbd6_6_2 : ∀ q ∈ blkd6_6_2, subd6_6 q = true := by
  unfold blkd6_6_2
  exact List.forall_mem_cons.2 ⟨subd6_6_64, List.forall_mem_cons.2 ⟨subd6_6_65, List.forall_mem_cons.2 ⟨subd6_6_66, List.forall_mem_cons.2 ⟨subd6_6_67, List.forall_mem_cons.2 ⟨subd6_6_68, List.forall_mem_cons.2 ⟨subd6_6_69, List.forall_mem_cons.2 ⟨subd6_6_70, List.forall_mem_cons.2 ⟨subd6_6_71, List.forall_mem_cons.2 ⟨subd6_6_72, List.forall_mem_cons.2 ⟨subd6_6_73, List.forall_mem_cons.2 ⟨subd6_6_74, List.forall_mem_cons.2 ⟨subd6_6_75, List.forall_mem_cons.2 ⟨subd6_6_76, List.forall_mem_cons.2 ⟨subd6_6_77, List.forall_mem_cons.2 ⟨subd6_6_78, List.forall_mem_cons.2 ⟨subd6_6_79, List.forall_mem_cons.2 ⟨subd6_6_80, List.forall_mem_cons.2 ⟨subd6_6_81, List.forall_mem_cons.2 ⟨subd6_6_82, List.forall_mem_cons.2 ⟨subd6_6_83, List.forall_mem_cons.2 ⟨subd6_6_84, List.forall_mem_cons.2 ⟨subd6_6_85, List.forall_mem_cons.2 ⟨subd6_6_86, List.forall_mem_cons.2 ⟨subd6_6_87, List.forall_mem_cons.2 ⟨subd6_6_88, List.forall_mem_cons.2 ⟨subd6_6_89, List.forall_mem_cons.2 ⟨subd6_6_90, List.forall_mem_cons.2 ⟨subd6_6_91, List.forall_mem_cons.2 ⟨subd6_6_92, List.forall_mem_cons.2 ⟨subd6_6_93, List.forall_mem_cons.2 ⟨subd6_6_94, List.forall_mem_cons.2 ⟨subd6_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
