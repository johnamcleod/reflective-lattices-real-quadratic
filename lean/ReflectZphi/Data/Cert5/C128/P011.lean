import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_0 : subd4_1 [-6] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-5, -4] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-5, -3] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-5, -2] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-5, -1] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-5, 0] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-5, 1] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-5, 2] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-5, 3] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-4, -5] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-4, -4] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-4, -3] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-4, -2] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-4, -1] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-4, 0] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [-4, 1] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [-4, 2] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [-4, 3] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [-4, 4] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [-3, -5] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [-3, -4] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [-3, -3] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [-3, -2] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [-3, -1] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [-3, 0] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [-3, 1] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [-3, 2] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [-3, 3] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [-3, 4] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [-3, 5] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [-2, -6] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [-2, -5] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [-2, -4] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_38 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_39 : subd4_1 [-2, 3] = true := by decide +kernel
theorem subd4_1_40 : subd4_1 [-2, 4] = true := by decide +kernel
theorem subd4_1_41 : subd4_1 [-2, 5] = true := by decide +kernel
theorem subd4_1_42 : subd4_1 [-1, -6] = true := by decide +kernel
theorem subd4_1_43 : subd4_1 [-1, -5] = true := by decide +kernel
theorem subd4_1_44 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_45 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_46 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_47 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_48 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_49 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_50 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_51 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_52 : subd4_1 [-1, 4] = true := by decide +kernel
theorem subd4_1_53 : subd4_1 [-1, 5] = true := by decide +kernel
theorem subd4_1_54 : subd4_1 [0, -6] = true := by decide +kernel
theorem subd4_1_55 : subd4_1 [0, -5] = true := by decide +kernel
theorem subd4_1_56 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_57 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_58 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_59 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_60 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_61 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_62 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_63 : subd4_1 [0, 3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_cons.2 ⟨subd4_1_38, List.forall_mem_cons.2 ⟨subd4_1_39, List.forall_mem_cons.2 ⟨subd4_1_40, List.forall_mem_cons.2 ⟨subd4_1_41, List.forall_mem_cons.2 ⟨subd4_1_42, List.forall_mem_cons.2 ⟨subd4_1_43, List.forall_mem_cons.2 ⟨subd4_1_44, List.forall_mem_cons.2 ⟨subd4_1_45, List.forall_mem_cons.2 ⟨subd4_1_46, List.forall_mem_cons.2 ⟨subd4_1_47, List.forall_mem_cons.2 ⟨subd4_1_48, List.forall_mem_cons.2 ⟨subd4_1_49, List.forall_mem_cons.2 ⟨subd4_1_50, List.forall_mem_cons.2 ⟨subd4_1_51, List.forall_mem_cons.2 ⟨subd4_1_52, List.forall_mem_cons.2 ⟨subd4_1_53, List.forall_mem_cons.2 ⟨subd4_1_54, List.forall_mem_cons.2 ⟨subd4_1_55, List.forall_mem_cons.2 ⟨subd4_1_56, List.forall_mem_cons.2 ⟨subd4_1_57, List.forall_mem_cons.2 ⟨subd4_1_58, List.forall_mem_cons.2 ⟨subd4_1_59, List.forall_mem_cons.2 ⟨subd4_1_60, List.forall_mem_cons.2 ⟨subd4_1_61, List.forall_mem_cons.2 ⟨subd4_1_62, List.forall_mem_cons.2 ⟨subd4_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_64 : subd4_1 [0, 4] = true := by decide +kernel
theorem subd4_1_65 : subd4_1 [0, 5] = true := by decide +kernel
theorem subd4_1_66 : subd4_1 [1, -6] = true := by decide +kernel
theorem subd4_1_67 : subd4_1 [1, -5] = true := by decide +kernel
theorem subd4_1_68 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_69 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_70 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_71 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_72 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_73 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_74 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_75 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_76 : subd4_1 [1, 4] = true := by decide +kernel
theorem subd4_1_77 : subd4_1 [1, 5] = true := by decide +kernel
theorem subd4_1_78 : subd4_1 [2, -6] = true := by decide +kernel
theorem subd4_1_79 : subd4_1 [2, -5] = true := by decide +kernel
theorem subd4_1_80 : subd4_1 [2, -4] = true := by decide +kernel
theorem subd4_1_81 : subd4_1 [2, -3] = true := by decide +kernel
theorem subd4_1_82 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_83 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_84 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_85 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_86 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_87 : subd4_1 [2, 3] = true := by decide +kernel
theorem subd4_1_88 : subd4_1 [2, 4] = true := by decide +kernel
theorem subd4_1_89 : subd4_1 [2, 5] = true := by decide +kernel
theorem subd4_1_90 : subd4_1 [3, -6] = true := by decide +kernel
theorem subd4_1_91 : subd4_1 [3, -5] = true := by decide +kernel
theorem subd4_1_92 : subd4_1 [3, -4] = true := by decide +kernel
theorem subd4_1_93 : subd4_1 [3, -3] = true := by decide +kernel
theorem subd4_1_94 : subd4_1 [3, -2] = true := by decide +kernel
theorem subd4_1_95 : subd4_1 [3, -1] = true := by decide +kernel
theorem sbd4_1_2 : ∀ q ∈ blkd4_1_2, subd4_1 q = true := by
  unfold blkd4_1_2
  exact List.forall_mem_cons.2 ⟨subd4_1_64, List.forall_mem_cons.2 ⟨subd4_1_65, List.forall_mem_cons.2 ⟨subd4_1_66, List.forall_mem_cons.2 ⟨subd4_1_67, List.forall_mem_cons.2 ⟨subd4_1_68, List.forall_mem_cons.2 ⟨subd4_1_69, List.forall_mem_cons.2 ⟨subd4_1_70, List.forall_mem_cons.2 ⟨subd4_1_71, List.forall_mem_cons.2 ⟨subd4_1_72, List.forall_mem_cons.2 ⟨subd4_1_73, List.forall_mem_cons.2 ⟨subd4_1_74, List.forall_mem_cons.2 ⟨subd4_1_75, List.forall_mem_cons.2 ⟨subd4_1_76, List.forall_mem_cons.2 ⟨subd4_1_77, List.forall_mem_cons.2 ⟨subd4_1_78, List.forall_mem_cons.2 ⟨subd4_1_79, List.forall_mem_cons.2 ⟨subd4_1_80, List.forall_mem_cons.2 ⟨subd4_1_81, List.forall_mem_cons.2 ⟨subd4_1_82, List.forall_mem_cons.2 ⟨subd4_1_83, List.forall_mem_cons.2 ⟨subd4_1_84, List.forall_mem_cons.2 ⟨subd4_1_85, List.forall_mem_cons.2 ⟨subd4_1_86, List.forall_mem_cons.2 ⟨subd4_1_87, List.forall_mem_cons.2 ⟨subd4_1_88, List.forall_mem_cons.2 ⟨subd4_1_89, List.forall_mem_cons.2 ⟨subd4_1_90, List.forall_mem_cons.2 ⟨subd4_1_91, List.forall_mem_cons.2 ⟨subd4_1_92, List.forall_mem_cons.2 ⟨subd4_1_93, List.forall_mem_cons.2 ⟨subd4_1_94, List.forall_mem_cons.2 ⟨subd4_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
