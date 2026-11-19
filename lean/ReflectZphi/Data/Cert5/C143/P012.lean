import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_1_32 : subd12_1 [-1, -4] = true := by decide +kernel
theorem subd12_1_33 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_34 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_35 : subd12_1 [-1, -1] = true := by decide +kernel
theorem subd12_1_36 : subd12_1 [-1, 0, -7] = true := by decide +kernel
theorem subd12_1_37 : subd12_1 [-1, 0, -6] = true := by decide +kernel
theorem subd12_1_38 : subd12_1 [-1, 0, -5] = true := by decide +kernel
theorem subd12_1_39 : subd12_1 [-1, 0, -4] = true := by decide +kernel
theorem subd12_1_40 : subd12_1 [-1, 0, -3] = true := by decide +kernel
theorem subd12_1_41 : subd12_1 [-1, 0, -2] = true := by decide +kernel
theorem subd12_1_42 : subd12_1 [-1, 0, -1] = true := by decide +kernel
theorem subd12_1_43 : subd12_1 [-1, 0, 0] = true := by decide +kernel
theorem subd12_1_44 : subd12_1 [-1, 0, 1] = true := by decide +kernel
theorem subd12_1_45 : subd12_1 [-1, 0, 2] = true := by decide +kernel
theorem subd12_1_46 : subd12_1 [-1, 0, 3] = true := by decide +kernel
theorem subd12_1_47 : subd12_1 [-1, 0, 4] = true := by decide +kernel
theorem subd12_1_48 : subd12_1 [-1, 0, 5] = true := by decide +kernel
theorem subd12_1_49 : subd12_1 [-1, 0, 6] = true := by decide +kernel
theorem subd12_1_50 : subd12_1 [-1, 0, 7] = true := by decide +kernel
theorem subd12_1_51 : subd12_1 [-1, 1] = true := by decide +kernel
theorem subd12_1_52 : subd12_1 [-1, 2] = true := by decide +kernel
theorem subd12_1_53 : subd12_1 [-1, 3] = true := by decide +kernel
theorem subd12_1_54 : subd12_1 [-1, 4] = true := by decide +kernel
theorem subd12_1_55 : subd12_1 [-1, 5] = true := by decide +kernel
theorem subd12_1_56 : subd12_1 [0, -6] = true := by decide +kernel
theorem subd12_1_57 : subd12_1 [0, -5] = true := by decide +kernel
theorem subd12_1_58 : subd12_1 [0, -4] = true := by decide +kernel
theorem subd12_1_59 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_60 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_61 : subd12_1 [0, -1] = true := by decide +kernel
theorem subd12_1_62 : subd12_1 [0, 0, -7] = true := by decide +kernel
theorem subd12_1_63 : subd12_1 [0, 0, -6] = true := by decide +kernel
theorem sbd12_1_1 : ∀ q ∈ blkd12_1_1, subd12_1 q = true := by
  unfold blkd12_1_1
  exact List.forall_mem_cons.2 ⟨subd12_1_32, List.forall_mem_cons.2 ⟨subd12_1_33, List.forall_mem_cons.2 ⟨subd12_1_34, List.forall_mem_cons.2 ⟨subd12_1_35, List.forall_mem_cons.2 ⟨subd12_1_36, List.forall_mem_cons.2 ⟨subd12_1_37, List.forall_mem_cons.2 ⟨subd12_1_38, List.forall_mem_cons.2 ⟨subd12_1_39, List.forall_mem_cons.2 ⟨subd12_1_40, List.forall_mem_cons.2 ⟨subd12_1_41, List.forall_mem_cons.2 ⟨subd12_1_42, List.forall_mem_cons.2 ⟨subd12_1_43, List.forall_mem_cons.2 ⟨subd12_1_44, List.forall_mem_cons.2 ⟨subd12_1_45, List.forall_mem_cons.2 ⟨subd12_1_46, List.forall_mem_cons.2 ⟨subd12_1_47, List.forall_mem_cons.2 ⟨subd12_1_48, List.forall_mem_cons.2 ⟨subd12_1_49, List.forall_mem_cons.2 ⟨subd12_1_50, List.forall_mem_cons.2 ⟨subd12_1_51, List.forall_mem_cons.2 ⟨subd12_1_52, List.forall_mem_cons.2 ⟨subd12_1_53, List.forall_mem_cons.2 ⟨subd12_1_54, List.forall_mem_cons.2 ⟨subd12_1_55, List.forall_mem_cons.2 ⟨subd12_1_56, List.forall_mem_cons.2 ⟨subd12_1_57, List.forall_mem_cons.2 ⟨subd12_1_58, List.forall_mem_cons.2 ⟨subd12_1_59, List.forall_mem_cons.2 ⟨subd12_1_60, List.forall_mem_cons.2 ⟨subd12_1_61, List.forall_mem_cons.2 ⟨subd12_1_62, List.forall_mem_cons.2 ⟨subd12_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_64 : subd12_1 [0, 0, -5] = true := by decide +kernel
theorem subd12_1_65 : subd12_1 [0, 0, -4] = true := by decide +kernel
theorem subd12_1_66 : subd12_1 [0, 0, -3] = true := by decide +kernel
theorem subd12_1_67 : subd12_1 [0, 0, -2] = true := by decide +kernel
theorem subd12_1_68 : subd12_1 [0, 0, -1] = true := by decide +kernel
theorem subd12_1_69 : subd12_1 [0, 0, 0] = true := by decide +kernel
theorem subd12_1_70 : subd12_1 [0, 0, 1] = true := by decide +kernel
theorem subd12_1_71 : subd12_1 [0, 0, 2] = true := by decide +kernel
theorem subd12_1_72 : subd12_1 [0, 0, 3] = true := by decide +kernel
theorem subd12_1_73 : subd12_1 [0, 0, 4] = true := by decide +kernel
theorem subd12_1_74 : subd12_1 [0, 0, 5] = true := by decide +kernel
theorem subd12_1_75 : subd12_1 [0, 0, 6] = true := by decide +kernel
theorem subd12_1_76 : subd12_1 [0, 1] = true := by decide +kernel
theorem subd12_1_77 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_78 : subd12_1 [0, 3] = true := by decide +kernel
theorem subd12_1_79 : subd12_1 [0, 4] = true := by decide +kernel
theorem subd12_1_80 : subd12_1 [0, 5] = true := by decide +kernel
theorem subd12_1_81 : subd12_1 [1, -6] = true := by decide +kernel
theorem subd12_1_82 : subd12_1 [1, -5] = true := by decide +kernel
theorem subd12_1_83 : subd12_1 [1, -4] = true := by decide +kernel
theorem subd12_1_84 : subd12_1 [1, -3] = true := by decide +kernel
theorem subd12_1_85 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_86 : subd12_1 [1, -1] = true := by decide +kernel
theorem subd12_1_87 : subd12_1 [1, 0, -8] = true := by decide +kernel
theorem subd12_1_88 : subd12_1 [1, 0, -7] = true := by decide +kernel
theorem subd12_1_89 : subd12_1 [1, 0, -6] = true := by decide +kernel
theorem subd12_1_90 : subd12_1 [1, 0, -5] = true := by decide +kernel
theorem subd12_1_91 : subd12_1 [1, 0, -4] = true := by decide +kernel
theorem subd12_1_92 : subd12_1 [1, 0, -3] = true := by decide +kernel
theorem subd12_1_93 : subd12_1 [1, 0, -2] = true := by decide +kernel
theorem subd12_1_94 : subd12_1 [1, 0, -1] = true := by decide +kernel
theorem subd12_1_95 : subd12_1 [1, 0, 0] = true := by decide +kernel
theorem sbd12_1_2 : ∀ q ∈ blkd12_1_2, subd12_1 q = true := by
  unfold blkd12_1_2
  exact List.forall_mem_cons.2 ⟨subd12_1_64, List.forall_mem_cons.2 ⟨subd12_1_65, List.forall_mem_cons.2 ⟨subd12_1_66, List.forall_mem_cons.2 ⟨subd12_1_67, List.forall_mem_cons.2 ⟨subd12_1_68, List.forall_mem_cons.2 ⟨subd12_1_69, List.forall_mem_cons.2 ⟨subd12_1_70, List.forall_mem_cons.2 ⟨subd12_1_71, List.forall_mem_cons.2 ⟨subd12_1_72, List.forall_mem_cons.2 ⟨subd12_1_73, List.forall_mem_cons.2 ⟨subd12_1_74, List.forall_mem_cons.2 ⟨subd12_1_75, List.forall_mem_cons.2 ⟨subd12_1_76, List.forall_mem_cons.2 ⟨subd12_1_77, List.forall_mem_cons.2 ⟨subd12_1_78, List.forall_mem_cons.2 ⟨subd12_1_79, List.forall_mem_cons.2 ⟨subd12_1_80, List.forall_mem_cons.2 ⟨subd12_1_81, List.forall_mem_cons.2 ⟨subd12_1_82, List.forall_mem_cons.2 ⟨subd12_1_83, List.forall_mem_cons.2 ⟨subd12_1_84, List.forall_mem_cons.2 ⟨subd12_1_85, List.forall_mem_cons.2 ⟨subd12_1_86, List.forall_mem_cons.2 ⟨subd12_1_87, List.forall_mem_cons.2 ⟨subd12_1_88, List.forall_mem_cons.2 ⟨subd12_1_89, List.forall_mem_cons.2 ⟨subd12_1_90, List.forall_mem_cons.2 ⟨subd12_1_91, List.forall_mem_cons.2 ⟨subd12_1_92, List.forall_mem_cons.2 ⟨subd12_1_93, List.forall_mem_cons.2 ⟨subd12_1_94, List.forall_mem_cons.2 ⟨subd12_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_96 : subd12_1 [1, 0, 1] = true := by decide +kernel
theorem subd12_1_97 : subd12_1 [1, 0, 2] = true := by decide +kernel
theorem subd12_1_98 : subd12_1 [1, 0, 3] = true := by decide +kernel
theorem subd12_1_99 : subd12_1 [1, 0, 4] = true := by decide +kernel
theorem subd12_1_100 : subd12_1 [1, 0, 5] = true := by decide +kernel
theorem subd12_1_101 : subd12_1 [1, 0, 6] = true := by decide +kernel
theorem subd12_1_102 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_103 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_104 : subd12_1 [1, 3] = true := by decide +kernel
theorem subd12_1_105 : subd12_1 [1, 4] = true := by decide +kernel
theorem subd12_1_106 : subd12_1 [1, 5] = true := by decide +kernel
theorem subd12_1_107 : subd12_1 [2, -5] = true := by decide +kernel
theorem subd12_1_108 : subd12_1 [2, -4] = true := by decide +kernel
theorem subd12_1_109 : subd12_1 [2, -3] = true := by decide +kernel
theorem subd12_1_110 : subd12_1 [2, -2] = true := by decide +kernel
theorem subd12_1_111 : subd12_1 [2, -1] = true := by decide +kernel
theorem subd12_1_112 : subd12_1 [2, 0] = true := by decide +kernel
theorem subd12_1_113 : subd12_1 [2, 1] = true := by decide +kernel
theorem subd12_1_114 : subd12_1 [2, 2] = true := by decide +kernel
theorem subd12_1_115 : subd12_1 [2, 3] = true := by decide +kernel
theorem subd12_1_116 : subd12_1 [2, 4] = true := by decide +kernel
theorem subd12_1_117 : subd12_1 [2, 5] = true := by decide +kernel
theorem subd12_1_118 : subd12_1 [3, -5] = true := by decide +kernel
theorem subd12_1_119 : subd12_1 [3, -4] = true := by decide +kernel
theorem subd12_1_120 : subd12_1 [3, -3] = true := by decide +kernel
theorem subd12_1_121 : subd12_1 [3, -2] = true := by decide +kernel
theorem subd12_1_122 : subd12_1 [3, -1] = true := by decide +kernel
theorem subd12_1_123 : subd12_1 [3, 0] = true := by decide +kernel
theorem subd12_1_124 : subd12_1 [3, 1] = true := by decide +kernel
theorem subd12_1_125 : subd12_1 [3, 2] = true := by decide +kernel
theorem subd12_1_126 : subd12_1 [3, 3] = true := by decide +kernel
theorem subd12_1_127 : subd12_1 [3, 4] = true := by decide +kernel
theorem sbd12_1_3 : ∀ q ∈ blkd12_1_3, subd12_1 q = true := by
  unfold blkd12_1_3
  exact List.forall_mem_cons.2 ⟨subd12_1_96, List.forall_mem_cons.2 ⟨subd12_1_97, List.forall_mem_cons.2 ⟨subd12_1_98, List.forall_mem_cons.2 ⟨subd12_1_99, List.forall_mem_cons.2 ⟨subd12_1_100, List.forall_mem_cons.2 ⟨subd12_1_101, List.forall_mem_cons.2 ⟨subd12_1_102, List.forall_mem_cons.2 ⟨subd12_1_103, List.forall_mem_cons.2 ⟨subd12_1_104, List.forall_mem_cons.2 ⟨subd12_1_105, List.forall_mem_cons.2 ⟨subd12_1_106, List.forall_mem_cons.2 ⟨subd12_1_107, List.forall_mem_cons.2 ⟨subd12_1_108, List.forall_mem_cons.2 ⟨subd12_1_109, List.forall_mem_cons.2 ⟨subd12_1_110, List.forall_mem_cons.2 ⟨subd12_1_111, List.forall_mem_cons.2 ⟨subd12_1_112, List.forall_mem_cons.2 ⟨subd12_1_113, List.forall_mem_cons.2 ⟨subd12_1_114, List.forall_mem_cons.2 ⟨subd12_1_115, List.forall_mem_cons.2 ⟨subd12_1_116, List.forall_mem_cons.2 ⟨subd12_1_117, List.forall_mem_cons.2 ⟨subd12_1_118, List.forall_mem_cons.2 ⟨subd12_1_119, List.forall_mem_cons.2 ⟨subd12_1_120, List.forall_mem_cons.2 ⟨subd12_1_121, List.forall_mem_cons.2 ⟨subd12_1_122, List.forall_mem_cons.2 ⟨subd12_1_123, List.forall_mem_cons.2 ⟨subd12_1_124, List.forall_mem_cons.2 ⟨subd12_1_125, List.forall_mem_cons.2 ⟨subd12_1_126, List.forall_mem_cons.2 ⟨subd12_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_128 : subd12_1 [4, -4] = true := by decide +kernel
theorem subd12_1_129 : subd12_1 [4, -3] = true := by decide +kernel
theorem subd12_1_130 : subd12_1 [4, -2] = true := by decide +kernel
theorem subd12_1_131 : subd12_1 [4, -1] = true := by decide +kernel
theorem subd12_1_132 : subd12_1 [4, 0] = true := by decide +kernel
theorem subd12_1_133 : subd12_1 [4, 1] = true := by decide +kernel
theorem subd12_1_134 : subd12_1 [4, 2] = true := by decide +kernel
theorem subd12_1_135 : subd12_1 [4, 3] = true := by decide +kernel
theorem subd12_1_136 : subd12_1 [5] = true := by decide +kernel
theorem sbd12_1_4 : ∀ q ∈ blkd12_1_4, subd12_1 q = true := by
  unfold blkd12_1_4
  exact List.forall_mem_cons.2 ⟨subd12_1_128, List.forall_mem_cons.2 ⟨subd12_1_129, List.forall_mem_cons.2 ⟨subd12_1_130, List.forall_mem_cons.2 ⟨subd12_1_131, List.forall_mem_cons.2 ⟨subd12_1_132, List.forall_mem_cons.2 ⟨subd12_1_133, List.forall_mem_cons.2 ⟨subd12_1_134, List.forall_mem_cons.2 ⟨subd12_1_135, List.forall_mem_cons.2 ⟨subd12_1_136, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
