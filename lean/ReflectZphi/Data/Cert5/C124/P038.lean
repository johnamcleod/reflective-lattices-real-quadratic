import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_11_32 : subd7_11 [-2, -1] = true := by decide +kernel
theorem subd7_11_33 : subd7_11 [-2, 0] = true := by decide +kernel
theorem subd7_11_34 : subd7_11 [-2, 1] = true := by decide +kernel
theorem subd7_11_35 : subd7_11 [-2, 2] = true := by decide +kernel
theorem subd7_11_36 : subd7_11 [-2, 3] = true := by decide +kernel
theorem subd7_11_37 : subd7_11 [-2, 4] = true := by decide +kernel
theorem subd7_11_38 : subd7_11 [-2, 5] = true := by decide +kernel
theorem subd7_11_39 : subd7_11 [-1, -8] = true := by decide +kernel
theorem subd7_11_40 : subd7_11 [-1, -7] = true := by decide +kernel
theorem subd7_11_41 : subd7_11 [-1, -6] = true := by decide +kernel
theorem subd7_11_42 : subd7_11 [-1, -5] = true := by decide +kernel
theorem subd7_11_43 : subd7_11 [-1, -4] = true := by decide +kernel
theorem subd7_11_44 : subd7_11 [-1, -3] = true := by decide +kernel
theorem subd7_11_45 : subd7_11 [-1, -2] = true := by decide +kernel
theorem subd7_11_46 : subd7_11 [-1, -1] = true := by decide +kernel
theorem subd7_11_47 : subd7_11 [-1, 0] = true := by decide +kernel
theorem subd7_11_48 : subd7_11 [-1, 1] = true := by decide +kernel
theorem subd7_11_49 : subd7_11 [-1, 2] = true := by decide +kernel
theorem subd7_11_50 : subd7_11 [-1, 3] = true := by decide +kernel
theorem subd7_11_51 : subd7_11 [-1, 4] = true := by decide +kernel
theorem subd7_11_52 : subd7_11 [-1, 5] = true := by decide +kernel
theorem subd7_11_53 : subd7_11 [-1, 6] = true := by decide +kernel
theorem subd7_11_54 : subd7_11 [0, -7] = true := by decide +kernel
theorem subd7_11_55 : subd7_11 [0, -6] = true := by decide +kernel
theorem subd7_11_56 : subd7_11 [0, -5] = true := by decide +kernel
theorem subd7_11_57 : subd7_11 [0, -4] = true := by decide +kernel
theorem subd7_11_58 : subd7_11 [0, -3] = true := by decide +kernel
theorem subd7_11_59 : subd7_11 [0, -2] = true := by decide +kernel
theorem subd7_11_60 : subd7_11 [0, -1] = true := by decide +kernel
theorem subd7_11_61 : subd7_11 [0, 0] = true := by decide +kernel
theorem subd7_11_62 : subd7_11 [0, 1] = true := by decide +kernel
theorem subd7_11_63 : subd7_11 [0, 2] = true := by decide +kernel
theorem sbd7_11_1 : ∀ q ∈ blkd7_11_1, subd7_11 q = true := by
  unfold blkd7_11_1
  exact List.forall_mem_cons.2 ⟨subd7_11_32, List.forall_mem_cons.2 ⟨subd7_11_33, List.forall_mem_cons.2 ⟨subd7_11_34, List.forall_mem_cons.2 ⟨subd7_11_35, List.forall_mem_cons.2 ⟨subd7_11_36, List.forall_mem_cons.2 ⟨subd7_11_37, List.forall_mem_cons.2 ⟨subd7_11_38, List.forall_mem_cons.2 ⟨subd7_11_39, List.forall_mem_cons.2 ⟨subd7_11_40, List.forall_mem_cons.2 ⟨subd7_11_41, List.forall_mem_cons.2 ⟨subd7_11_42, List.forall_mem_cons.2 ⟨subd7_11_43, List.forall_mem_cons.2 ⟨subd7_11_44, List.forall_mem_cons.2 ⟨subd7_11_45, List.forall_mem_cons.2 ⟨subd7_11_46, List.forall_mem_cons.2 ⟨subd7_11_47, List.forall_mem_cons.2 ⟨subd7_11_48, List.forall_mem_cons.2 ⟨subd7_11_49, List.forall_mem_cons.2 ⟨subd7_11_50, List.forall_mem_cons.2 ⟨subd7_11_51, List.forall_mem_cons.2 ⟨subd7_11_52, List.forall_mem_cons.2 ⟨subd7_11_53, List.forall_mem_cons.2 ⟨subd7_11_54, List.forall_mem_cons.2 ⟨subd7_11_55, List.forall_mem_cons.2 ⟨subd7_11_56, List.forall_mem_cons.2 ⟨subd7_11_57, List.forall_mem_cons.2 ⟨subd7_11_58, List.forall_mem_cons.2 ⟨subd7_11_59, List.forall_mem_cons.2 ⟨subd7_11_60, List.forall_mem_cons.2 ⟨subd7_11_61, List.forall_mem_cons.2 ⟨subd7_11_62, List.forall_mem_cons.2 ⟨subd7_11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_11_64 : subd7_11 [0, 3] = true := by decide +kernel
theorem subd7_11_65 : subd7_11 [0, 4] = true := by decide +kernel
theorem subd7_11_66 : subd7_11 [0, 5] = true := by decide +kernel
theorem subd7_11_67 : subd7_11 [0, 6] = true := by decide +kernel
theorem subd7_11_68 : subd7_11 [1, -7] = true := by decide +kernel
theorem subd7_11_69 : subd7_11 [1, -6] = true := by decide +kernel
theorem subd7_11_70 : subd7_11 [1, -5] = true := by decide +kernel
theorem subd7_11_71 : subd7_11 [1, -4] = true := by decide +kernel
theorem subd7_11_72 : subd7_11 [1, -3] = true := by decide +kernel
theorem subd7_11_73 : subd7_11 [1, -2] = true := by decide +kernel
theorem subd7_11_74 : subd7_11 [1, -1] = true := by decide +kernel
theorem subd7_11_75 : subd7_11 [1, 0] = true := by decide +kernel
theorem subd7_11_76 : subd7_11 [1, 1] = true := by decide +kernel
theorem subd7_11_77 : subd7_11 [1, 2] = true := by decide +kernel
theorem subd7_11_78 : subd7_11 [1, 3] = true := by decide +kernel
theorem subd7_11_79 : subd7_11 [1, 4] = true := by decide +kernel
theorem subd7_11_80 : subd7_11 [1, 5] = true := by decide +kernel
theorem subd7_11_81 : subd7_11 [1, 6] = true := by decide +kernel
theorem subd7_11_82 : subd7_11 [1, 7] = true := by decide +kernel
theorem subd7_11_83 : subd7_11 [2, -6] = true := by decide +kernel
theorem subd7_11_84 : subd7_11 [2, -5] = true := by decide +kernel
theorem subd7_11_85 : subd7_11 [2, -4] = true := by decide +kernel
theorem subd7_11_86 : subd7_11 [2, -3] = true := by decide +kernel
theorem subd7_11_87 : subd7_11 [2, -2] = true := by decide +kernel
theorem subd7_11_88 : subd7_11 [2, -1] = true := by decide +kernel
theorem subd7_11_89 : subd7_11 [2, 0] = true := by decide +kernel
theorem subd7_11_90 : subd7_11 [2, 1] = true := by decide +kernel
theorem subd7_11_91 : subd7_11 [2, 2] = true := by decide +kernel
theorem subd7_11_92 : subd7_11 [2, 3] = true := by decide +kernel
theorem subd7_11_93 : subd7_11 [2, 4] = true := by decide +kernel
theorem subd7_11_94 : subd7_11 [2, 5] = true := by decide +kernel
theorem subd7_11_95 : subd7_11 [2, 6] = true := by decide +kernel
theorem sbd7_11_2 : ∀ q ∈ blkd7_11_2, subd7_11 q = true := by
  unfold blkd7_11_2
  exact List.forall_mem_cons.2 ⟨subd7_11_64, List.forall_mem_cons.2 ⟨subd7_11_65, List.forall_mem_cons.2 ⟨subd7_11_66, List.forall_mem_cons.2 ⟨subd7_11_67, List.forall_mem_cons.2 ⟨subd7_11_68, List.forall_mem_cons.2 ⟨subd7_11_69, List.forall_mem_cons.2 ⟨subd7_11_70, List.forall_mem_cons.2 ⟨subd7_11_71, List.forall_mem_cons.2 ⟨subd7_11_72, List.forall_mem_cons.2 ⟨subd7_11_73, List.forall_mem_cons.2 ⟨subd7_11_74, List.forall_mem_cons.2 ⟨subd7_11_75, List.forall_mem_cons.2 ⟨subd7_11_76, List.forall_mem_cons.2 ⟨subd7_11_77, List.forall_mem_cons.2 ⟨subd7_11_78, List.forall_mem_cons.2 ⟨subd7_11_79, List.forall_mem_cons.2 ⟨subd7_11_80, List.forall_mem_cons.2 ⟨subd7_11_81, List.forall_mem_cons.2 ⟨subd7_11_82, List.forall_mem_cons.2 ⟨subd7_11_83, List.forall_mem_cons.2 ⟨subd7_11_84, List.forall_mem_cons.2 ⟨subd7_11_85, List.forall_mem_cons.2 ⟨subd7_11_86, List.forall_mem_cons.2 ⟨subd7_11_87, List.forall_mem_cons.2 ⟨subd7_11_88, List.forall_mem_cons.2 ⟨subd7_11_89, List.forall_mem_cons.2 ⟨subd7_11_90, List.forall_mem_cons.2 ⟨subd7_11_91, List.forall_mem_cons.2 ⟨subd7_11_92, List.forall_mem_cons.2 ⟨subd7_11_93, List.forall_mem_cons.2 ⟨subd7_11_94, List.forall_mem_cons.2 ⟨subd7_11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_11_96 : subd7_11 [2, 7] = true := by decide +kernel
theorem subd7_11_97 : subd7_11 [3, -5] = true := by decide +kernel
theorem subd7_11_98 : subd7_11 [3, -4] = true := by decide +kernel
theorem subd7_11_99 : subd7_11 [3, -3] = true := by decide +kernel
theorem subd7_11_100 : subd7_11 [3, -2] = true := by decide +kernel
theorem subd7_11_101 : subd7_11 [3, -1] = true := by decide +kernel
theorem subd7_11_102 : subd7_11 [3, 0] = true := by decide +kernel
theorem subd7_11_103 : subd7_11 [3, 1] = true := by decide +kernel
theorem subd7_11_104 : subd7_11 [3, 2] = true := by decide +kernel
theorem subd7_11_105 : subd7_11 [3, 3] = true := by decide +kernel
theorem subd7_11_106 : subd7_11 [3, 4] = true := by decide +kernel
theorem subd7_11_107 : subd7_11 [3, 5] = true := by decide +kernel
theorem subd7_11_108 : subd7_11 [3, 6] = true := by decide +kernel
theorem subd7_11_109 : subd7_11 [3, 7] = true := by decide +kernel
theorem subd7_11_110 : subd7_11 [4, -4] = true := by decide +kernel
theorem subd7_11_111 : subd7_11 [4, -3] = true := by decide +kernel
theorem subd7_11_112 : subd7_11 [4, -2] = true := by decide +kernel
theorem subd7_11_113 : subd7_11 [4, -1] = true := by decide +kernel
theorem subd7_11_114 : subd7_11 [4, 0] = true := by decide +kernel
theorem subd7_11_115 : subd7_11 [4, 1] = true := by decide +kernel
theorem subd7_11_116 : subd7_11 [4, 2] = true := by decide +kernel
theorem subd7_11_117 : subd7_11 [4, 3] = true := by decide +kernel
theorem subd7_11_118 : subd7_11 [4, 4] = true := by decide +kernel
theorem subd7_11_119 : subd7_11 [4, 5] = true := by decide +kernel
theorem subd7_11_120 : subd7_11 [4, 6] = true := by decide +kernel
theorem subd7_11_121 : subd7_11 [5] = true := by decide +kernel
theorem sbd7_11_3 : ∀ q ∈ blkd7_11_3, subd7_11 q = true := by
  unfold blkd7_11_3
  exact List.forall_mem_cons.2 ⟨subd7_11_96, List.forall_mem_cons.2 ⟨subd7_11_97, List.forall_mem_cons.2 ⟨subd7_11_98, List.forall_mem_cons.2 ⟨subd7_11_99, List.forall_mem_cons.2 ⟨subd7_11_100, List.forall_mem_cons.2 ⟨subd7_11_101, List.forall_mem_cons.2 ⟨subd7_11_102, List.forall_mem_cons.2 ⟨subd7_11_103, List.forall_mem_cons.2 ⟨subd7_11_104, List.forall_mem_cons.2 ⟨subd7_11_105, List.forall_mem_cons.2 ⟨subd7_11_106, List.forall_mem_cons.2 ⟨subd7_11_107, List.forall_mem_cons.2 ⟨subd7_11_108, List.forall_mem_cons.2 ⟨subd7_11_109, List.forall_mem_cons.2 ⟨subd7_11_110, List.forall_mem_cons.2 ⟨subd7_11_111, List.forall_mem_cons.2 ⟨subd7_11_112, List.forall_mem_cons.2 ⟨subd7_11_113, List.forall_mem_cons.2 ⟨subd7_11_114, List.forall_mem_cons.2 ⟨subd7_11_115, List.forall_mem_cons.2 ⟨subd7_11_116, List.forall_mem_cons.2 ⟨subd7_11_117, List.forall_mem_cons.2 ⟨subd7_11_118, List.forall_mem_cons.2 ⟨subd7_11_119, List.forall_mem_cons.2 ⟨subd7_11_120, List.forall_mem_cons.2 ⟨subd7_11_121, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_12 : ldCheck G d7_12.U d7_12.ms ldd7_12 = true := by decide +kernel
theorem pre_okd7_12 : subPre G cell7 d7_12 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
