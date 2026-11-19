import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_32 : subd10_0 [-3, -5] = true := by decide +kernel
theorem subd10_0_33 : subd10_0 [-3, -4] = true := by decide +kernel
theorem subd10_0_34 : subd10_0 [-3, -3] = true := by decide +kernel
theorem subd10_0_35 : subd10_0 [-3, -2] = true := by decide +kernel
theorem subd10_0_36 : subd10_0 [-3, -1] = true := by decide +kernel
theorem subd10_0_37 : subd10_0 [-3, 0] = true := by decide +kernel
theorem subd10_0_38 : subd10_0 [-3, 1] = true := by decide +kernel
theorem subd10_0_39 : subd10_0 [-3, 2] = true := by decide +kernel
theorem subd10_0_40 : subd10_0 [-3, 3] = true := by decide +kernel
theorem subd10_0_41 : subd10_0 [-3, 4] = true := by decide +kernel
theorem subd10_0_42 : subd10_0 [-3, 5] = true := by decide +kernel
theorem subd10_0_43 : subd10_0 [-3, 6] = true := by decide +kernel
theorem subd10_0_44 : subd10_0 [-3, 7] = true := by decide +kernel
theorem subd10_0_45 : subd10_0 [-2, -7] = true := by decide +kernel
theorem subd10_0_46 : subd10_0 [-2, -6] = true := by decide +kernel
theorem subd10_0_47 : subd10_0 [-2, -5] = true := by decide +kernel
theorem subd10_0_48 : subd10_0 [-2, -4] = true := by decide +kernel
theorem subd10_0_49 : subd10_0 [-2, -3] = true := by decide +kernel
theorem subd10_0_50 : subd10_0 [-2, -2] = true := by decide +kernel
theorem subd10_0_51 : subd10_0 [-2, -1] = true := by decide +kernel
theorem subd10_0_52 : subd10_0 [-2, 0] = true := by decide +kernel
theorem subd10_0_53 : subd10_0 [-2, 1] = true := by decide +kernel
theorem subd10_0_54 : subd10_0 [-2, 2] = true := by decide +kernel
theorem subd10_0_55 : subd10_0 [-2, 3] = true := by decide +kernel
theorem subd10_0_56 : subd10_0 [-2, 4] = true := by decide +kernel
theorem subd10_0_57 : subd10_0 [-2, 5] = true := by decide +kernel
theorem subd10_0_58 : subd10_0 [-2, 6] = true := by decide +kernel
theorem subd10_0_59 : subd10_0 [-2, 7] = true := by decide +kernel
theorem subd10_0_60 : subd10_0 [-1, -7] = true := by decide +kernel
theorem subd10_0_61 : subd10_0 [-1, -6] = true := by decide +kernel
theorem subd10_0_62 : subd10_0 [-1, -5] = true := by decide +kernel
theorem subd10_0_63 : subd10_0 [-1, -4] = true := by decide +kernel
theorem sbd10_0_1 : ∀ q ∈ blkd10_0_1, subd10_0 q = true := by
  unfold blkd10_0_1
  exact List.forall_mem_cons.2 ⟨subd10_0_32, List.forall_mem_cons.2 ⟨subd10_0_33, List.forall_mem_cons.2 ⟨subd10_0_34, List.forall_mem_cons.2 ⟨subd10_0_35, List.forall_mem_cons.2 ⟨subd10_0_36, List.forall_mem_cons.2 ⟨subd10_0_37, List.forall_mem_cons.2 ⟨subd10_0_38, List.forall_mem_cons.2 ⟨subd10_0_39, List.forall_mem_cons.2 ⟨subd10_0_40, List.forall_mem_cons.2 ⟨subd10_0_41, List.forall_mem_cons.2 ⟨subd10_0_42, List.forall_mem_cons.2 ⟨subd10_0_43, List.forall_mem_cons.2 ⟨subd10_0_44, List.forall_mem_cons.2 ⟨subd10_0_45, List.forall_mem_cons.2 ⟨subd10_0_46, List.forall_mem_cons.2 ⟨subd10_0_47, List.forall_mem_cons.2 ⟨subd10_0_48, List.forall_mem_cons.2 ⟨subd10_0_49, List.forall_mem_cons.2 ⟨subd10_0_50, List.forall_mem_cons.2 ⟨subd10_0_51, List.forall_mem_cons.2 ⟨subd10_0_52, List.forall_mem_cons.2 ⟨subd10_0_53, List.forall_mem_cons.2 ⟨subd10_0_54, List.forall_mem_cons.2 ⟨subd10_0_55, List.forall_mem_cons.2 ⟨subd10_0_56, List.forall_mem_cons.2 ⟨subd10_0_57, List.forall_mem_cons.2 ⟨subd10_0_58, List.forall_mem_cons.2 ⟨subd10_0_59, List.forall_mem_cons.2 ⟨subd10_0_60, List.forall_mem_cons.2 ⟨subd10_0_61, List.forall_mem_cons.2 ⟨subd10_0_62, List.forall_mem_cons.2 ⟨subd10_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_64 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_65 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_66 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_67 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_68 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_69 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_70 : subd10_0 [-1, 3] = true := by decide +kernel
theorem subd10_0_71 : subd10_0 [-1, 4] = true := by decide +kernel
theorem subd10_0_72 : subd10_0 [-1, 5] = true := by decide +kernel
theorem subd10_0_73 : subd10_0 [-1, 6] = true := by decide +kernel
theorem subd10_0_74 : subd10_0 [-1, 7] = true := by decide +kernel
theorem subd10_0_75 : subd10_0 [0, -8] = true := by decide +kernel
theorem subd10_0_76 : subd10_0 [0, -7] = true := by decide +kernel
theorem subd10_0_77 : subd10_0 [0, -6] = true := by decide +kernel
theorem subd10_0_78 : subd10_0 [0, -5] = true := by decide +kernel
theorem subd10_0_79 : subd10_0 [0, -4] = true := by decide +kernel
theorem subd10_0_80 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_81 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_82 : subd10_0 [0, -1, -8] = true := by decide +kernel
theorem subd10_0_83 : subd10_0 [0, -1, -7] = true := by decide +kernel
theorem subd10_0_84 : subd10_0 [0, -1, -6] = true := by decide +kernel
theorem subd10_0_85 : subd10_0 [0, -1, -5] = true := by decide +kernel
theorem subd10_0_86 : subd10_0 [0, -1, -4] = true := by decide +kernel
theorem subd10_0_87 : subd10_0 [0, -1, -3] = true := by decide +kernel
theorem subd10_0_88 : subd10_0 [0, -1, -2] = true := by decide +kernel
theorem subd10_0_89 : subd10_0 [0, -1, -1] = true := by decide +kernel
theorem subd10_0_90 : subd10_0 [0, -1, 0] = true := by decide +kernel
theorem subd10_0_91 : subd10_0 [0, -1, 1] = true := by decide +kernel
theorem subd10_0_92 : subd10_0 [0, -1, 2] = true := by decide +kernel
theorem subd10_0_93 : subd10_0 [0, -1, 3] = true := by decide +kernel
theorem subd10_0_94 : subd10_0 [0, -1, 4] = true := by decide +kernel
theorem subd10_0_95 : subd10_0 [0, -1, 5] = true := by decide +kernel
theorem sbd10_0_2 : ∀ q ∈ blkd10_0_2, subd10_0 q = true := by
  unfold blkd10_0_2
  exact List.forall_mem_cons.2 ⟨subd10_0_64, List.forall_mem_cons.2 ⟨subd10_0_65, List.forall_mem_cons.2 ⟨subd10_0_66, List.forall_mem_cons.2 ⟨subd10_0_67, List.forall_mem_cons.2 ⟨subd10_0_68, List.forall_mem_cons.2 ⟨subd10_0_69, List.forall_mem_cons.2 ⟨subd10_0_70, List.forall_mem_cons.2 ⟨subd10_0_71, List.forall_mem_cons.2 ⟨subd10_0_72, List.forall_mem_cons.2 ⟨subd10_0_73, List.forall_mem_cons.2 ⟨subd10_0_74, List.forall_mem_cons.2 ⟨subd10_0_75, List.forall_mem_cons.2 ⟨subd10_0_76, List.forall_mem_cons.2 ⟨subd10_0_77, List.forall_mem_cons.2 ⟨subd10_0_78, List.forall_mem_cons.2 ⟨subd10_0_79, List.forall_mem_cons.2 ⟨subd10_0_80, List.forall_mem_cons.2 ⟨subd10_0_81, List.forall_mem_cons.2 ⟨subd10_0_82, List.forall_mem_cons.2 ⟨subd10_0_83, List.forall_mem_cons.2 ⟨subd10_0_84, List.forall_mem_cons.2 ⟨subd10_0_85, List.forall_mem_cons.2 ⟨subd10_0_86, List.forall_mem_cons.2 ⟨subd10_0_87, List.forall_mem_cons.2 ⟨subd10_0_88, List.forall_mem_cons.2 ⟨subd10_0_89, List.forall_mem_cons.2 ⟨subd10_0_90, List.forall_mem_cons.2 ⟨subd10_0_91, List.forall_mem_cons.2 ⟨subd10_0_92, List.forall_mem_cons.2 ⟨subd10_0_93, List.forall_mem_cons.2 ⟨subd10_0_94, List.forall_mem_cons.2 ⟨subd10_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_96 : subd10_0 [0, -1, 6] = true := by decide +kernel
theorem subd10_0_97 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_98 : subd10_0 [0, 1, -7] = true := by decide +kernel
theorem subd10_0_99 : subd10_0 [0, 1, -6] = true := by decide +kernel
theorem subd10_0_100 : subd10_0 [0, 1, -5] = true := by decide +kernel
theorem subd10_0_101 : subd10_0 [0, 1, -4] = true := by decide +kernel
theorem subd10_0_102 : subd10_0 [0, 1, -3] = true := by decide +kernel
theorem subd10_0_103 : subd10_0 [0, 1, -2] = true := by decide +kernel
theorem subd10_0_104 : subd10_0 [0, 1, -1] = true := by decide +kernel
theorem subd10_0_105 : subd10_0 [0, 1, 0] = true := by decide +kernel
theorem subd10_0_106 : subd10_0 [0, 1, 1] = true := by decide +kernel
theorem subd10_0_107 : subd10_0 [0, 1, 2] = true := by decide +kernel
theorem subd10_0_108 : subd10_0 [0, 1, 3] = true := by decide +kernel
theorem subd10_0_109 : subd10_0 [0, 1, 4] = true := by decide +kernel
theorem subd10_0_110 : subd10_0 [0, 1, 5] = true := by decide +kernel
theorem subd10_0_111 : subd10_0 [0, 1, 6] = true := by decide +kernel
theorem subd10_0_112 : subd10_0 [0, 1, 7] = true := by decide +kernel
theorem subd10_0_113 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_114 : subd10_0 [0, 3] = true := by decide +kernel
theorem subd10_0_115 : subd10_0 [0, 4] = true := by decide +kernel
theorem subd10_0_116 : subd10_0 [0, 5] = true := by decide +kernel
theorem subd10_0_117 : subd10_0 [0, 6] = true := by decide +kernel
theorem subd10_0_118 : subd10_0 [0, 7] = true := by decide +kernel
theorem subd10_0_119 : subd10_0 [1, -8] = true := by decide +kernel
theorem subd10_0_120 : subd10_0 [1, -7] = true := by decide +kernel
theorem subd10_0_121 : subd10_0 [1, -6] = true := by decide +kernel
theorem subd10_0_122 : subd10_0 [1, -5] = true := by decide +kernel
theorem subd10_0_123 : subd10_0 [1, -4] = true := by decide +kernel
theorem subd10_0_124 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_125 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_126 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_127 : subd10_0 [1, 0] = true := by decide +kernel
theorem sbd10_0_3 : ∀ q ∈ blkd10_0_3, subd10_0 q = true := by
  unfold blkd10_0_3
  exact List.forall_mem_cons.2 ⟨subd10_0_96, List.forall_mem_cons.2 ⟨subd10_0_97, List.forall_mem_cons.2 ⟨subd10_0_98, List.forall_mem_cons.2 ⟨subd10_0_99, List.forall_mem_cons.2 ⟨subd10_0_100, List.forall_mem_cons.2 ⟨subd10_0_101, List.forall_mem_cons.2 ⟨subd10_0_102, List.forall_mem_cons.2 ⟨subd10_0_103, List.forall_mem_cons.2 ⟨subd10_0_104, List.forall_mem_cons.2 ⟨subd10_0_105, List.forall_mem_cons.2 ⟨subd10_0_106, List.forall_mem_cons.2 ⟨subd10_0_107, List.forall_mem_cons.2 ⟨subd10_0_108, List.forall_mem_cons.2 ⟨subd10_0_109, List.forall_mem_cons.2 ⟨subd10_0_110, List.forall_mem_cons.2 ⟨subd10_0_111, List.forall_mem_cons.2 ⟨subd10_0_112, List.forall_mem_cons.2 ⟨subd10_0_113, List.forall_mem_cons.2 ⟨subd10_0_114, List.forall_mem_cons.2 ⟨subd10_0_115, List.forall_mem_cons.2 ⟨subd10_0_116, List.forall_mem_cons.2 ⟨subd10_0_117, List.forall_mem_cons.2 ⟨subd10_0_118, List.forall_mem_cons.2 ⟨subd10_0_119, List.forall_mem_cons.2 ⟨subd10_0_120, List.forall_mem_cons.2 ⟨subd10_0_121, List.forall_mem_cons.2 ⟨subd10_0_122, List.forall_mem_cons.2 ⟨subd10_0_123, List.forall_mem_cons.2 ⟨subd10_0_124, List.forall_mem_cons.2 ⟨subd10_0_125, List.forall_mem_cons.2 ⟨subd10_0_126, List.forall_mem_cons.2 ⟨subd10_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
