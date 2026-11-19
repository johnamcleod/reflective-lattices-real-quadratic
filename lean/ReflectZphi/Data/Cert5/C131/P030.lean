import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_0_0 : subd14_0 [-5] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-4, -7] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [-4, -6] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [-4, -5] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [-4, -4] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [-4, -3] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [-4, -2] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [-4, -1] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [-4, 0] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [-4, 1] = true := by decide +kernel
theorem subd14_0_10 : subd14_0 [-4, 2] = true := by decide +kernel
theorem subd14_0_11 : subd14_0 [-3, -7] = true := by decide +kernel
theorem subd14_0_12 : subd14_0 [-3, -6] = true := by decide +kernel
theorem subd14_0_13 : subd14_0 [-3, -5] = true := by decide +kernel
theorem subd14_0_14 : subd14_0 [-3, -4] = true := by decide +kernel
theorem subd14_0_15 : subd14_0 [-3, -3] = true := by decide +kernel
theorem subd14_0_16 : subd14_0 [-3, -2] = true := by decide +kernel
theorem subd14_0_17 : subd14_0 [-3, -1] = true := by decide +kernel
theorem subd14_0_18 : subd14_0 [-3, 0] = true := by decide +kernel
theorem subd14_0_19 : subd14_0 [-3, 1] = true := by decide +kernel
theorem subd14_0_20 : subd14_0 [-3, 2] = true := by decide +kernel
theorem subd14_0_21 : subd14_0 [-3, 3] = true := by decide +kernel
theorem subd14_0_22 : subd14_0 [-2, -7] = true := by decide +kernel
theorem subd14_0_23 : subd14_0 [-2, -6] = true := by decide +kernel
theorem subd14_0_24 : subd14_0 [-2, -5] = true := by decide +kernel
theorem subd14_0_25 : subd14_0 [-2, -4] = true := by decide +kernel
theorem subd14_0_26 : subd14_0 [-2, -3] = true := by decide +kernel
theorem subd14_0_27 : subd14_0 [-2, -2] = true := by decide +kernel
theorem subd14_0_28 : subd14_0 [-2, -1] = true := by decide +kernel
theorem subd14_0_29 : subd14_0 [-2, 0] = true := by decide +kernel
theorem subd14_0_30 : subd14_0 [-2, 1] = true := by decide +kernel
theorem subd14_0_31 : subd14_0 [-2, 2] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_cons.2 ⟨subd14_0_10, List.forall_mem_cons.2 ⟨subd14_0_11, List.forall_mem_cons.2 ⟨subd14_0_12, List.forall_mem_cons.2 ⟨subd14_0_13, List.forall_mem_cons.2 ⟨subd14_0_14, List.forall_mem_cons.2 ⟨subd14_0_15, List.forall_mem_cons.2 ⟨subd14_0_16, List.forall_mem_cons.2 ⟨subd14_0_17, List.forall_mem_cons.2 ⟨subd14_0_18, List.forall_mem_cons.2 ⟨subd14_0_19, List.forall_mem_cons.2 ⟨subd14_0_20, List.forall_mem_cons.2 ⟨subd14_0_21, List.forall_mem_cons.2 ⟨subd14_0_22, List.forall_mem_cons.2 ⟨subd14_0_23, List.forall_mem_cons.2 ⟨subd14_0_24, List.forall_mem_cons.2 ⟨subd14_0_25, List.forall_mem_cons.2 ⟨subd14_0_26, List.forall_mem_cons.2 ⟨subd14_0_27, List.forall_mem_cons.2 ⟨subd14_0_28, List.forall_mem_cons.2 ⟨subd14_0_29, List.forall_mem_cons.2 ⟨subd14_0_30, List.forall_mem_cons.2 ⟨subd14_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_32 : subd14_0 [-2, 3] = true := by decide +kernel
theorem subd14_0_33 : subd14_0 [-2, 4] = true := by decide +kernel
theorem subd14_0_34 : subd14_0 [-1, -7] = true := by decide +kernel
theorem subd14_0_35 : subd14_0 [-1, -6] = true := by decide +kernel
theorem subd14_0_36 : subd14_0 [-1, -5] = true := by decide +kernel
theorem subd14_0_37 : subd14_0 [-1, -4] = true := by decide +kernel
theorem subd14_0_38 : subd14_0 [-1, -3] = true := by decide +kernel
theorem subd14_0_39 : subd14_0 [-1, -2] = true := by decide +kernel
theorem subd14_0_40 : subd14_0 [-1, -1] = true := by decide +kernel
theorem subd14_0_41 : subd14_0 [-1, 0] = true := by decide +kernel
theorem subd14_0_42 : subd14_0 [-1, 1] = true := by decide +kernel
theorem subd14_0_43 : subd14_0 [-1, 2] = true := by decide +kernel
theorem subd14_0_44 : subd14_0 [-1, 3] = true := by decide +kernel
theorem subd14_0_45 : subd14_0 [-1, 4] = true := by decide +kernel
theorem subd14_0_46 : subd14_0 [-1, 5] = true := by decide +kernel
theorem subd14_0_47 : subd14_0 [0, -7] = true := by decide +kernel
theorem subd14_0_48 : subd14_0 [0, -6] = true := by decide +kernel
theorem subd14_0_49 : subd14_0 [0, -5] = true := by decide +kernel
theorem subd14_0_50 : subd14_0 [0, -4] = true := by decide +kernel
theorem subd14_0_51 : subd14_0 [0, -3] = true := by decide +kernel
theorem subd14_0_52 : subd14_0 [0, -2] = true := by decide +kernel
theorem subd14_0_53 : subd14_0 [0, -1] = true := by decide +kernel
theorem subd14_0_54 : subd14_0 [0, 0] = true := by decide +kernel
theorem subd14_0_55 : subd14_0 [0, 1] = true := by decide +kernel
theorem subd14_0_56 : subd14_0 [0, 2] = true := by decide +kernel
theorem subd14_0_57 : subd14_0 [0, 3] = true := by decide +kernel
theorem subd14_0_58 : subd14_0 [0, 4] = true := by decide +kernel
theorem subd14_0_59 : subd14_0 [0, 5] = true := by decide +kernel
theorem subd14_0_60 : subd14_0 [0, 6] = true := by decide +kernel
theorem subd14_0_61 : subd14_0 [1, -6] = true := by decide +kernel
theorem subd14_0_62 : subd14_0 [1, -5] = true := by decide +kernel
theorem subd14_0_63 : subd14_0 [1, -4] = true := by decide +kernel
theorem sbd14_0_1 : ∀ q ∈ blkd14_0_1, subd14_0 q = true := by
  unfold blkd14_0_1
  exact List.forall_mem_cons.2 ⟨subd14_0_32, List.forall_mem_cons.2 ⟨subd14_0_33, List.forall_mem_cons.2 ⟨subd14_0_34, List.forall_mem_cons.2 ⟨subd14_0_35, List.forall_mem_cons.2 ⟨subd14_0_36, List.forall_mem_cons.2 ⟨subd14_0_37, List.forall_mem_cons.2 ⟨subd14_0_38, List.forall_mem_cons.2 ⟨subd14_0_39, List.forall_mem_cons.2 ⟨subd14_0_40, List.forall_mem_cons.2 ⟨subd14_0_41, List.forall_mem_cons.2 ⟨subd14_0_42, List.forall_mem_cons.2 ⟨subd14_0_43, List.forall_mem_cons.2 ⟨subd14_0_44, List.forall_mem_cons.2 ⟨subd14_0_45, List.forall_mem_cons.2 ⟨subd14_0_46, List.forall_mem_cons.2 ⟨subd14_0_47, List.forall_mem_cons.2 ⟨subd14_0_48, List.forall_mem_cons.2 ⟨subd14_0_49, List.forall_mem_cons.2 ⟨subd14_0_50, List.forall_mem_cons.2 ⟨subd14_0_51, List.forall_mem_cons.2 ⟨subd14_0_52, List.forall_mem_cons.2 ⟨subd14_0_53, List.forall_mem_cons.2 ⟨subd14_0_54, List.forall_mem_cons.2 ⟨subd14_0_55, List.forall_mem_cons.2 ⟨subd14_0_56, List.forall_mem_cons.2 ⟨subd14_0_57, List.forall_mem_cons.2 ⟨subd14_0_58, List.forall_mem_cons.2 ⟨subd14_0_59, List.forall_mem_cons.2 ⟨subd14_0_60, List.forall_mem_cons.2 ⟨subd14_0_61, List.forall_mem_cons.2 ⟨subd14_0_62, List.forall_mem_cons.2 ⟨subd14_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_64 : subd14_0 [1, -3] = true := by decide +kernel
theorem subd14_0_65 : subd14_0 [1, -2] = true := by decide +kernel
theorem subd14_0_66 : subd14_0 [1, -1] = true := by decide +kernel
theorem subd14_0_67 : subd14_0 [1, 0] = true := by decide +kernel
theorem subd14_0_68 : subd14_0 [1, 1] = true := by decide +kernel
theorem subd14_0_69 : subd14_0 [1, 2] = true := by decide +kernel
theorem subd14_0_70 : subd14_0 [1, 3] = true := by decide +kernel
theorem subd14_0_71 : subd14_0 [1, 4] = true := by decide +kernel
theorem subd14_0_72 : subd14_0 [1, 5] = true := by decide +kernel
theorem subd14_0_73 : subd14_0 [1, 6] = true := by decide +kernel
theorem subd14_0_74 : subd14_0 [2, -5] = true := by decide +kernel
theorem subd14_0_75 : subd14_0 [2, -4] = true := by decide +kernel
theorem subd14_0_76 : subd14_0 [2, -3] = true := by decide +kernel
theorem subd14_0_77 : subd14_0 [2, -2] = true := by decide +kernel
theorem subd14_0_78 : subd14_0 [2, -1] = true := by decide +kernel
theorem subd14_0_79 : subd14_0 [2, 0] = true := by decide +kernel
theorem subd14_0_80 : subd14_0 [2, 1] = true := by decide +kernel
theorem subd14_0_81 : subd14_0 [2, 2] = true := by decide +kernel
theorem subd14_0_82 : subd14_0 [2, 3] = true := by decide +kernel
theorem subd14_0_83 : subd14_0 [2, 4] = true := by decide +kernel
theorem subd14_0_84 : subd14_0 [2, 5] = true := by decide +kernel
theorem subd14_0_85 : subd14_0 [2, 6] = true := by decide +kernel
theorem subd14_0_86 : subd14_0 [3, -4] = true := by decide +kernel
theorem subd14_0_87 : subd14_0 [3, -3] = true := by decide +kernel
theorem subd14_0_88 : subd14_0 [3, -2] = true := by decide +kernel
theorem subd14_0_89 : subd14_0 [3, -1] = true := by decide +kernel
theorem subd14_0_90 : subd14_0 [3, 0] = true := by decide +kernel
theorem subd14_0_91 : subd14_0 [3, 1] = true := by decide +kernel
theorem subd14_0_92 : subd14_0 [3, 2] = true := by decide +kernel
theorem subd14_0_93 : subd14_0 [3, 3] = true := by decide +kernel
theorem subd14_0_94 : subd14_0 [3, 4] = true := by decide +kernel
theorem subd14_0_95 : subd14_0 [3, 5] = true := by decide +kernel
theorem sbd14_0_2 : ∀ q ∈ blkd14_0_2, subd14_0 q = true := by
  unfold blkd14_0_2
  exact List.forall_mem_cons.2 ⟨subd14_0_64, List.forall_mem_cons.2 ⟨subd14_0_65, List.forall_mem_cons.2 ⟨subd14_0_66, List.forall_mem_cons.2 ⟨subd14_0_67, List.forall_mem_cons.2 ⟨subd14_0_68, List.forall_mem_cons.2 ⟨subd14_0_69, List.forall_mem_cons.2 ⟨subd14_0_70, List.forall_mem_cons.2 ⟨subd14_0_71, List.forall_mem_cons.2 ⟨subd14_0_72, List.forall_mem_cons.2 ⟨subd14_0_73, List.forall_mem_cons.2 ⟨subd14_0_74, List.forall_mem_cons.2 ⟨subd14_0_75, List.forall_mem_cons.2 ⟨subd14_0_76, List.forall_mem_cons.2 ⟨subd14_0_77, List.forall_mem_cons.2 ⟨subd14_0_78, List.forall_mem_cons.2 ⟨subd14_0_79, List.forall_mem_cons.2 ⟨subd14_0_80, List.forall_mem_cons.2 ⟨subd14_0_81, List.forall_mem_cons.2 ⟨subd14_0_82, List.forall_mem_cons.2 ⟨subd14_0_83, List.forall_mem_cons.2 ⟨subd14_0_84, List.forall_mem_cons.2 ⟨subd14_0_85, List.forall_mem_cons.2 ⟨subd14_0_86, List.forall_mem_cons.2 ⟨subd14_0_87, List.forall_mem_cons.2 ⟨subd14_0_88, List.forall_mem_cons.2 ⟨subd14_0_89, List.forall_mem_cons.2 ⟨subd14_0_90, List.forall_mem_cons.2 ⟨subd14_0_91, List.forall_mem_cons.2 ⟨subd14_0_92, List.forall_mem_cons.2 ⟨subd14_0_93, List.forall_mem_cons.2 ⟨subd14_0_94, List.forall_mem_cons.2 ⟨subd14_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_96 : subd14_0 [3, 6] = true := by decide +kernel
theorem subd14_0_97 : subd14_0 [4, -3] = true := by decide +kernel
theorem subd14_0_98 : subd14_0 [4, -2] = true := by decide +kernel
theorem subd14_0_99 : subd14_0 [4, -1] = true := by decide +kernel
theorem subd14_0_100 : subd14_0 [4, 0] = true := by decide +kernel
theorem subd14_0_101 : subd14_0 [4, 1] = true := by decide +kernel
theorem subd14_0_102 : subd14_0 [4, 2] = true := by decide +kernel
theorem subd14_0_103 : subd14_0 [4, 3] = true := by decide +kernel
theorem subd14_0_104 : subd14_0 [4, 4] = true := by decide +kernel
theorem subd14_0_105 : subd14_0 [4, 5] = true := by decide +kernel
theorem subd14_0_106 : subd14_0 [4, 6] = true := by decide +kernel
theorem subd14_0_107 : subd14_0 [5] = true := by decide +kernel
theorem sbd14_0_3 : ∀ q ∈ blkd14_0_3, subd14_0 q = true := by
  unfold blkd14_0_3
  exact List.forall_mem_cons.2 ⟨subd14_0_96, List.forall_mem_cons.2 ⟨subd14_0_97, List.forall_mem_cons.2 ⟨subd14_0_98, List.forall_mem_cons.2 ⟨subd14_0_99, List.forall_mem_cons.2 ⟨subd14_0_100, List.forall_mem_cons.2 ⟨subd14_0_101, List.forall_mem_cons.2 ⟨subd14_0_102, List.forall_mem_cons.2 ⟨subd14_0_103, List.forall_mem_cons.2 ⟨subd14_0_104, List.forall_mem_cons.2 ⟨subd14_0_105, List.forall_mem_cons.2 ⟨subd14_0_106, List.forall_mem_cons.2 ⟨subd14_0_107, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
