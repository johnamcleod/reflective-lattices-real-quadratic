import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_6_0 : subd9_6 [-6] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-5, -6] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-5, -5] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-5, -4] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-5, -3] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-5, -2] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [-5, -1] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [-5, 0] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [-5, 1] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [-4, -7] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [-4, -6] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [-4, -5] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [-4, -4] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [-4, -3] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [-4, -2] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [-4, -1] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [-4, 0] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [-4, 1] = true := by decide +kernel
theorem subd9_6_18 : subd9_6 [-4, 2] = true := by decide +kernel
theorem subd9_6_19 : subd9_6 [-3, -7] = true := by decide +kernel
theorem subd9_6_20 : subd9_6 [-3, -6] = true := by decide +kernel
theorem subd9_6_21 : subd9_6 [-3, -5] = true := by decide +kernel
theorem subd9_6_22 : subd9_6 [-3, -4] = true := by decide +kernel
theorem subd9_6_23 : subd9_6 [-3, -3] = true := by decide +kernel
theorem subd9_6_24 : subd9_6 [-3, -2] = true := by decide +kernel
theorem subd9_6_25 : subd9_6 [-3, -1] = true := by decide +kernel
theorem subd9_6_26 : subd9_6 [-3, 0] = true := by decide +kernel
theorem subd9_6_27 : subd9_6 [-3, 1] = true := by decide +kernel
theorem subd9_6_28 : subd9_6 [-3, 2] = true := by decide +kernel
theorem subd9_6_29 : subd9_6 [-3, 3] = true := by decide +kernel
theorem subd9_6_30 : subd9_6 [-2, -7] = true := by decide +kernel
theorem subd9_6_31 : subd9_6 [-2, -6] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_cons.2 ⟨subd9_6_18, List.forall_mem_cons.2 ⟨subd9_6_19, List.forall_mem_cons.2 ⟨subd9_6_20, List.forall_mem_cons.2 ⟨subd9_6_21, List.forall_mem_cons.2 ⟨subd9_6_22, List.forall_mem_cons.2 ⟨subd9_6_23, List.forall_mem_cons.2 ⟨subd9_6_24, List.forall_mem_cons.2 ⟨subd9_6_25, List.forall_mem_cons.2 ⟨subd9_6_26, List.forall_mem_cons.2 ⟨subd9_6_27, List.forall_mem_cons.2 ⟨subd9_6_28, List.forall_mem_cons.2 ⟨subd9_6_29, List.forall_mem_cons.2 ⟨subd9_6_30, List.forall_mem_cons.2 ⟨subd9_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_32 : subd9_6 [-2, -5] = true := by decide +kernel
theorem subd9_6_33 : subd9_6 [-2, -4] = true := by decide +kernel
theorem subd9_6_34 : subd9_6 [-2, -3] = true := by decide +kernel
theorem subd9_6_35 : subd9_6 [-2, -2] = true := by decide +kernel
theorem subd9_6_36 : subd9_6 [-2, -1] = true := by decide +kernel
theorem subd9_6_37 : subd9_6 [-2, 0] = true := by decide +kernel
theorem subd9_6_38 : subd9_6 [-2, 1] = true := by decide +kernel
theorem subd9_6_39 : subd9_6 [-2, 2] = true := by decide +kernel
theorem subd9_6_40 : subd9_6 [-2, 3] = true := by decide +kernel
theorem subd9_6_41 : subd9_6 [-2, 4] = true := by decide +kernel
theorem subd9_6_42 : subd9_6 [-1, -6] = true := by decide +kernel
theorem subd9_6_43 : subd9_6 [-1, -5] = true := by decide +kernel
theorem subd9_6_44 : subd9_6 [-1, -4] = true := by decide +kernel
theorem subd9_6_45 : subd9_6 [-1, -3] = true := by decide +kernel
theorem subd9_6_46 : subd9_6 [-1, -2] = true := by decide +kernel
theorem subd9_6_47 : subd9_6 [-1, -1] = true := by decide +kernel
theorem subd9_6_48 : subd9_6 [-1, 0] = true := by decide +kernel
theorem subd9_6_49 : subd9_6 [-1, 1] = true := by decide +kernel
theorem subd9_6_50 : subd9_6 [-1, 2] = true := by decide +kernel
theorem subd9_6_51 : subd9_6 [-1, 3] = true := by decide +kernel
theorem subd9_6_52 : subd9_6 [-1, 4] = true := by decide +kernel
theorem subd9_6_53 : subd9_6 [0, -6] = true := by decide +kernel
theorem subd9_6_54 : subd9_6 [0, -5] = true := by decide +kernel
theorem subd9_6_55 : subd9_6 [0, -4] = true := by decide +kernel
theorem subd9_6_56 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_57 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_58 : subd9_6 [0, -1] = true := by decide +kernel
theorem subd9_6_59 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_60 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_61 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_62 : subd9_6 [0, 3] = true := by decide +kernel
theorem subd9_6_63 : subd9_6 [0, 4] = true := by decide +kernel
theorem sbd9_6_1 : ∀ q ∈ blkd9_6_1, subd9_6 q = true := by
  unfold blkd9_6_1
  exact List.forall_mem_cons.2 ⟨subd9_6_32, List.forall_mem_cons.2 ⟨subd9_6_33, List.forall_mem_cons.2 ⟨subd9_6_34, List.forall_mem_cons.2 ⟨subd9_6_35, List.forall_mem_cons.2 ⟨subd9_6_36, List.forall_mem_cons.2 ⟨subd9_6_37, List.forall_mem_cons.2 ⟨subd9_6_38, List.forall_mem_cons.2 ⟨subd9_6_39, List.forall_mem_cons.2 ⟨subd9_6_40, List.forall_mem_cons.2 ⟨subd9_6_41, List.forall_mem_cons.2 ⟨subd9_6_42, List.forall_mem_cons.2 ⟨subd9_6_43, List.forall_mem_cons.2 ⟨subd9_6_44, List.forall_mem_cons.2 ⟨subd9_6_45, List.forall_mem_cons.2 ⟨subd9_6_46, List.forall_mem_cons.2 ⟨subd9_6_47, List.forall_mem_cons.2 ⟨subd9_6_48, List.forall_mem_cons.2 ⟨subd9_6_49, List.forall_mem_cons.2 ⟨subd9_6_50, List.forall_mem_cons.2 ⟨subd9_6_51, List.forall_mem_cons.2 ⟨subd9_6_52, List.forall_mem_cons.2 ⟨subd9_6_53, List.forall_mem_cons.2 ⟨subd9_6_54, List.forall_mem_cons.2 ⟨subd9_6_55, List.forall_mem_cons.2 ⟨subd9_6_56, List.forall_mem_cons.2 ⟨subd9_6_57, List.forall_mem_cons.2 ⟨subd9_6_58, List.forall_mem_cons.2 ⟨subd9_6_59, List.forall_mem_cons.2 ⟨subd9_6_60, List.forall_mem_cons.2 ⟨subd9_6_61, List.forall_mem_cons.2 ⟨subd9_6_62, List.forall_mem_cons.2 ⟨subd9_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_64 : subd9_6 [0, 5] = true := by decide +kernel
theorem subd9_6_65 : subd9_6 [1, -5] = true := by decide +kernel
theorem subd9_6_66 : subd9_6 [1, -4] = true := by decide +kernel
theorem subd9_6_67 : subd9_6 [1, -3] = true := by decide +kernel
theorem subd9_6_68 : subd9_6 [1, -2] = true := by decide +kernel
theorem subd9_6_69 : subd9_6 [1, -1] = true := by decide +kernel
theorem subd9_6_70 : subd9_6 [1, 0] = true := by decide +kernel
theorem subd9_6_71 : subd9_6 [1, 1] = true := by decide +kernel
theorem subd9_6_72 : subd9_6 [1, 2] = true := by decide +kernel
theorem subd9_6_73 : subd9_6 [1, 3] = true := by decide +kernel
theorem subd9_6_74 : subd9_6 [1, 4] = true := by decide +kernel
theorem subd9_6_75 : subd9_6 [1, 5] = true := by decide +kernel
theorem subd9_6_76 : subd9_6 [2, -5] = true := by decide +kernel
theorem subd9_6_77 : subd9_6 [2, -4] = true := by decide +kernel
theorem subd9_6_78 : subd9_6 [2, -3] = true := by decide +kernel
theorem subd9_6_79 : subd9_6 [2, -2] = true := by decide +kernel
theorem subd9_6_80 : subd9_6 [2, -1] = true := by decide +kernel
theorem subd9_6_81 : subd9_6 [2, 0] = true := by decide +kernel
theorem subd9_6_82 : subd9_6 [2, 1] = true := by decide +kernel
theorem subd9_6_83 : subd9_6 [2, 2] = true := by decide +kernel
theorem subd9_6_84 : subd9_6 [2, 3] = true := by decide +kernel
theorem subd9_6_85 : subd9_6 [2, 4] = true := by decide +kernel
theorem subd9_6_86 : subd9_6 [2, 5] = true := by decide +kernel
theorem subd9_6_87 : subd9_6 [2, 6] = true := by decide +kernel
theorem subd9_6_88 : subd9_6 [3, -4] = true := by decide +kernel
theorem subd9_6_89 : subd9_6 [3, -3] = true := by decide +kernel
theorem subd9_6_90 : subd9_6 [3, -2] = true := by decide +kernel
theorem subd9_6_91 : subd9_6 [3, -1] = true := by decide +kernel
theorem subd9_6_92 : subd9_6 [3, 0] = true := by decide +kernel
theorem subd9_6_93 : subd9_6 [3, 1] = true := by decide +kernel
theorem subd9_6_94 : subd9_6 [3, 2] = true := by decide +kernel
theorem subd9_6_95 : subd9_6 [3, 3] = true := by decide +kernel
theorem sbd9_6_2 : ∀ q ∈ blkd9_6_2, subd9_6 q = true := by
  unfold blkd9_6_2
  exact List.forall_mem_cons.2 ⟨subd9_6_64, List.forall_mem_cons.2 ⟨subd9_6_65, List.forall_mem_cons.2 ⟨subd9_6_66, List.forall_mem_cons.2 ⟨subd9_6_67, List.forall_mem_cons.2 ⟨subd9_6_68, List.forall_mem_cons.2 ⟨subd9_6_69, List.forall_mem_cons.2 ⟨subd9_6_70, List.forall_mem_cons.2 ⟨subd9_6_71, List.forall_mem_cons.2 ⟨subd9_6_72, List.forall_mem_cons.2 ⟨subd9_6_73, List.forall_mem_cons.2 ⟨subd9_6_74, List.forall_mem_cons.2 ⟨subd9_6_75, List.forall_mem_cons.2 ⟨subd9_6_76, List.forall_mem_cons.2 ⟨subd9_6_77, List.forall_mem_cons.2 ⟨subd9_6_78, List.forall_mem_cons.2 ⟨subd9_6_79, List.forall_mem_cons.2 ⟨subd9_6_80, List.forall_mem_cons.2 ⟨subd9_6_81, List.forall_mem_cons.2 ⟨subd9_6_82, List.forall_mem_cons.2 ⟨subd9_6_83, List.forall_mem_cons.2 ⟨subd9_6_84, List.forall_mem_cons.2 ⟨subd9_6_85, List.forall_mem_cons.2 ⟨subd9_6_86, List.forall_mem_cons.2 ⟨subd9_6_87, List.forall_mem_cons.2 ⟨subd9_6_88, List.forall_mem_cons.2 ⟨subd9_6_89, List.forall_mem_cons.2 ⟨subd9_6_90, List.forall_mem_cons.2 ⟨subd9_6_91, List.forall_mem_cons.2 ⟨subd9_6_92, List.forall_mem_cons.2 ⟨subd9_6_93, List.forall_mem_cons.2 ⟨subd9_6_94, List.forall_mem_cons.2 ⟨subd9_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_6_96 : subd9_6 [3, 4] = true := by decide +kernel
theorem subd9_6_97 : subd9_6 [3, 5] = true := by decide +kernel
theorem subd9_6_98 : subd9_6 [3, 6] = true := by decide +kernel
theorem subd9_6_99 : subd9_6 [4, -3] = true := by decide +kernel
theorem subd9_6_100 : subd9_6 [4, -2] = true := by decide +kernel
theorem subd9_6_101 : subd9_6 [4, -1] = true := by decide +kernel
theorem subd9_6_102 : subd9_6 [4, 0] = true := by decide +kernel
theorem subd9_6_103 : subd9_6 [4, 1] = true := by decide +kernel
theorem subd9_6_104 : subd9_6 [4, 2] = true := by decide +kernel
theorem subd9_6_105 : subd9_6 [4, 3] = true := by decide +kernel
theorem subd9_6_106 : subd9_6 [4, 4] = true := by decide +kernel
theorem subd9_6_107 : subd9_6 [4, 5] = true := by decide +kernel
theorem subd9_6_108 : subd9_6 [4, 6] = true := by decide +kernel
theorem subd9_6_109 : subd9_6 [5, -2] = true := by decide +kernel
theorem subd9_6_110 : subd9_6 [5, -1] = true := by decide +kernel
theorem subd9_6_111 : subd9_6 [5, 0] = true := by decide +kernel
theorem subd9_6_112 : subd9_6 [5, 1] = true := by decide +kernel
theorem subd9_6_113 : subd9_6 [5, 2] = true := by decide +kernel
theorem subd9_6_114 : subd9_6 [5, 3] = true := by decide +kernel
theorem subd9_6_115 : subd9_6 [5, 4] = true := by decide +kernel
theorem subd9_6_116 : subd9_6 [5, 5] = true := by decide +kernel
theorem subd9_6_117 : subd9_6 [6] = true := by decide +kernel
theorem sbd9_6_3 : ∀ q ∈ blkd9_6_3, subd9_6 q = true := by
  unfold blkd9_6_3
  exact List.forall_mem_cons.2 ⟨subd9_6_96, List.forall_mem_cons.2 ⟨subd9_6_97, List.forall_mem_cons.2 ⟨subd9_6_98, List.forall_mem_cons.2 ⟨subd9_6_99, List.forall_mem_cons.2 ⟨subd9_6_100, List.forall_mem_cons.2 ⟨subd9_6_101, List.forall_mem_cons.2 ⟨subd9_6_102, List.forall_mem_cons.2 ⟨subd9_6_103, List.forall_mem_cons.2 ⟨subd9_6_104, List.forall_mem_cons.2 ⟨subd9_6_105, List.forall_mem_cons.2 ⟨subd9_6_106, List.forall_mem_cons.2 ⟨subd9_6_107, List.forall_mem_cons.2 ⟨subd9_6_108, List.forall_mem_cons.2 ⟨subd9_6_109, List.forall_mem_cons.2 ⟨subd9_6_110, List.forall_mem_cons.2 ⟨subd9_6_111, List.forall_mem_cons.2 ⟨subd9_6_112, List.forall_mem_cons.2 ⟨subd9_6_113, List.forall_mem_cons.2 ⟨subd9_6_114, List.forall_mem_cons.2 ⟨subd9_6_115, List.forall_mem_cons.2 ⟨subd9_6_116, List.forall_mem_cons.2 ⟨subd9_6_117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
