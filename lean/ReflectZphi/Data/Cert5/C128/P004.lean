import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_1_32 : subd3_1 [-2, -4] = true := by decide +kernel
theorem subd3_1_33 : subd3_1 [-2, -3] = true := by decide +kernel
theorem subd3_1_34 : subd3_1 [-2, -2] = true := by decide +kernel
theorem subd3_1_35 : subd3_1 [-2, -1] = true := by decide +kernel
theorem subd3_1_36 : subd3_1 [-2, 0] = true := by decide +kernel
theorem subd3_1_37 : subd3_1 [-2, 1] = true := by decide +kernel
theorem subd3_1_38 : subd3_1 [-2, 2] = true := by decide +kernel
theorem subd3_1_39 : subd3_1 [-2, 3] = true := by decide +kernel
theorem subd3_1_40 : subd3_1 [-2, 4] = true := by decide +kernel
theorem subd3_1_41 : subd3_1 [-1, -7] = true := by decide +kernel
theorem subd3_1_42 : subd3_1 [-1, -6] = true := by decide +kernel
theorem subd3_1_43 : subd3_1 [-1, -5] = true := by decide +kernel
theorem subd3_1_44 : subd3_1 [-1, -4] = true := by decide +kernel
theorem subd3_1_45 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_46 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_47 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_48 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_49 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_50 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_51 : subd3_1 [-1, 3] = true := by decide +kernel
theorem subd3_1_52 : subd3_1 [-1, 4] = true := by decide +kernel
theorem subd3_1_53 : subd3_1 [-1, 5] = true := by decide +kernel
theorem subd3_1_54 : subd3_1 [0, -6] = true := by decide +kernel
theorem subd3_1_55 : subd3_1 [0, -5] = true := by decide +kernel
theorem subd3_1_56 : subd3_1 [0, -4] = true := by decide +kernel
theorem subd3_1_57 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_58 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_59 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_60 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_61 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_62 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_63 : subd3_1 [0, 3] = true := by decide +kernel
theorem sbd3_1_1 : ∀ q ∈ blkd3_1_1, subd3_1 q = true := by
  unfold blkd3_1_1
  exact List.forall_mem_cons.2 ⟨subd3_1_32, List.forall_mem_cons.2 ⟨subd3_1_33, List.forall_mem_cons.2 ⟨subd3_1_34, List.forall_mem_cons.2 ⟨subd3_1_35, List.forall_mem_cons.2 ⟨subd3_1_36, List.forall_mem_cons.2 ⟨subd3_1_37, List.forall_mem_cons.2 ⟨subd3_1_38, List.forall_mem_cons.2 ⟨subd3_1_39, List.forall_mem_cons.2 ⟨subd3_1_40, List.forall_mem_cons.2 ⟨subd3_1_41, List.forall_mem_cons.2 ⟨subd3_1_42, List.forall_mem_cons.2 ⟨subd3_1_43, List.forall_mem_cons.2 ⟨subd3_1_44, List.forall_mem_cons.2 ⟨subd3_1_45, List.forall_mem_cons.2 ⟨subd3_1_46, List.forall_mem_cons.2 ⟨subd3_1_47, List.forall_mem_cons.2 ⟨subd3_1_48, List.forall_mem_cons.2 ⟨subd3_1_49, List.forall_mem_cons.2 ⟨subd3_1_50, List.forall_mem_cons.2 ⟨subd3_1_51, List.forall_mem_cons.2 ⟨subd3_1_52, List.forall_mem_cons.2 ⟨subd3_1_53, List.forall_mem_cons.2 ⟨subd3_1_54, List.forall_mem_cons.2 ⟨subd3_1_55, List.forall_mem_cons.2 ⟨subd3_1_56, List.forall_mem_cons.2 ⟨subd3_1_57, List.forall_mem_cons.2 ⟨subd3_1_58, List.forall_mem_cons.2 ⟨subd3_1_59, List.forall_mem_cons.2 ⟨subd3_1_60, List.forall_mem_cons.2 ⟨subd3_1_61, List.forall_mem_cons.2 ⟨subd3_1_62, List.forall_mem_cons.2 ⟨subd3_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_64 : subd3_1 [0, 4] = true := by decide +kernel
theorem subd3_1_65 : subd3_1 [0, 5] = true := by decide +kernel
theorem subd3_1_66 : subd3_1 [1, -6] = true := by decide +kernel
theorem subd3_1_67 : subd3_1 [1, -5] = true := by decide +kernel
theorem subd3_1_68 : subd3_1 [1, -4] = true := by decide +kernel
theorem subd3_1_69 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_70 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_71 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_72 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_73 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_74 : subd3_1 [1, 2] = true := by decide +kernel
theorem subd3_1_75 : subd3_1 [1, 3] = true := by decide +kernel
theorem subd3_1_76 : subd3_1 [1, 4] = true := by decide +kernel
theorem subd3_1_77 : subd3_1 [1, 5] = true := by decide +kernel
theorem subd3_1_78 : subd3_1 [1, 6] = true := by decide +kernel
theorem subd3_1_79 : subd3_1 [2, -5] = true := by decide +kernel
theorem subd3_1_80 : subd3_1 [2, -4] = true := by decide +kernel
theorem subd3_1_81 : subd3_1 [2, -3] = true := by decide +kernel
theorem subd3_1_82 : subd3_1 [2, -2] = true := by decide +kernel
theorem subd3_1_83 : subd3_1 [2, -1] = true := by decide +kernel
theorem subd3_1_84 : subd3_1 [2, 0] = true := by decide +kernel
theorem subd3_1_85 : subd3_1 [2, 1] = true := by decide +kernel
theorem subd3_1_86 : subd3_1 [2, 2] = true := by decide +kernel
theorem subd3_1_87 : subd3_1 [2, 3] = true := by decide +kernel
theorem subd3_1_88 : subd3_1 [2, 4] = true := by decide +kernel
theorem subd3_1_89 : subd3_1 [2, 5] = true := by decide +kernel
theorem subd3_1_90 : subd3_1 [2, 6] = true := by decide +kernel
theorem subd3_1_91 : subd3_1 [3, -4] = true := by decide +kernel
theorem subd3_1_92 : subd3_1 [3, -3] = true := by decide +kernel
theorem subd3_1_93 : subd3_1 [3, -2] = true := by decide +kernel
theorem subd3_1_94 : subd3_1 [3, -1] = true := by decide +kernel
theorem subd3_1_95 : subd3_1 [3, 0] = true := by decide +kernel
theorem sbd3_1_2 : ∀ q ∈ blkd3_1_2, subd3_1 q = true := by
  unfold blkd3_1_2
  exact List.forall_mem_cons.2 ⟨subd3_1_64, List.forall_mem_cons.2 ⟨subd3_1_65, List.forall_mem_cons.2 ⟨subd3_1_66, List.forall_mem_cons.2 ⟨subd3_1_67, List.forall_mem_cons.2 ⟨subd3_1_68, List.forall_mem_cons.2 ⟨subd3_1_69, List.forall_mem_cons.2 ⟨subd3_1_70, List.forall_mem_cons.2 ⟨subd3_1_71, List.forall_mem_cons.2 ⟨subd3_1_72, List.forall_mem_cons.2 ⟨subd3_1_73, List.forall_mem_cons.2 ⟨subd3_1_74, List.forall_mem_cons.2 ⟨subd3_1_75, List.forall_mem_cons.2 ⟨subd3_1_76, List.forall_mem_cons.2 ⟨subd3_1_77, List.forall_mem_cons.2 ⟨subd3_1_78, List.forall_mem_cons.2 ⟨subd3_1_79, List.forall_mem_cons.2 ⟨subd3_1_80, List.forall_mem_cons.2 ⟨subd3_1_81, List.forall_mem_cons.2 ⟨subd3_1_82, List.forall_mem_cons.2 ⟨subd3_1_83, List.forall_mem_cons.2 ⟨subd3_1_84, List.forall_mem_cons.2 ⟨subd3_1_85, List.forall_mem_cons.2 ⟨subd3_1_86, List.forall_mem_cons.2 ⟨subd3_1_87, List.forall_mem_cons.2 ⟨subd3_1_88, List.forall_mem_cons.2 ⟨subd3_1_89, List.forall_mem_cons.2 ⟨subd3_1_90, List.forall_mem_cons.2 ⟨subd3_1_91, List.forall_mem_cons.2 ⟨subd3_1_92, List.forall_mem_cons.2 ⟨subd3_1_93, List.forall_mem_cons.2 ⟨subd3_1_94, List.forall_mem_cons.2 ⟨subd3_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_96 : subd3_1 [3, 1] = true := by decide +kernel
theorem subd3_1_97 : subd3_1 [3, 2] = true := by decide +kernel
theorem subd3_1_98 : subd3_1 [3, 3] = true := by decide +kernel
theorem subd3_1_99 : subd3_1 [3, 4] = true := by decide +kernel
theorem subd3_1_100 : subd3_1 [3, 5] = true := by decide +kernel
theorem subd3_1_101 : subd3_1 [3, 6] = true := by decide +kernel
theorem subd3_1_102 : subd3_1 [4, -3] = true := by decide +kernel
theorem subd3_1_103 : subd3_1 [4, -2] = true := by decide +kernel
theorem subd3_1_104 : subd3_1 [4, -1] = true := by decide +kernel
theorem subd3_1_105 : subd3_1 [4, 0] = true := by decide +kernel
theorem subd3_1_106 : subd3_1 [4, 1] = true := by decide +kernel
theorem subd3_1_107 : subd3_1 [4, 2] = true := by decide +kernel
theorem subd3_1_108 : subd3_1 [4, 3] = true := by decide +kernel
theorem subd3_1_109 : subd3_1 [4, 4] = true := by decide +kernel
theorem subd3_1_110 : subd3_1 [4, 5] = true := by decide +kernel
theorem subd3_1_111 : subd3_1 [4, 6] = true := by decide +kernel
theorem subd3_1_112 : subd3_1 [5, -1] = true := by decide +kernel
theorem subd3_1_113 : subd3_1 [5, 0] = true := by decide +kernel
theorem subd3_1_114 : subd3_1 [5, 1] = true := by decide +kernel
theorem subd3_1_115 : subd3_1 [5, 2] = true := by decide +kernel
theorem subd3_1_116 : subd3_1 [5, 3] = true := by decide +kernel
theorem subd3_1_117 : subd3_1 [5, 4] = true := by decide +kernel
theorem subd3_1_118 : subd3_1 [5, 5] = true := by decide +kernel
theorem subd3_1_119 : subd3_1 [6] = true := by decide +kernel
theorem sbd3_1_3 : ∀ q ∈ blkd3_1_3, subd3_1 q = true := by
  unfold blkd3_1_3
  exact List.forall_mem_cons.2 ⟨subd3_1_96, List.forall_mem_cons.2 ⟨subd3_1_97, List.forall_mem_cons.2 ⟨subd3_1_98, List.forall_mem_cons.2 ⟨subd3_1_99, List.forall_mem_cons.2 ⟨subd3_1_100, List.forall_mem_cons.2 ⟨subd3_1_101, List.forall_mem_cons.2 ⟨subd3_1_102, List.forall_mem_cons.2 ⟨subd3_1_103, List.forall_mem_cons.2 ⟨subd3_1_104, List.forall_mem_cons.2 ⟨subd3_1_105, List.forall_mem_cons.2 ⟨subd3_1_106, List.forall_mem_cons.2 ⟨subd3_1_107, List.forall_mem_cons.2 ⟨subd3_1_108, List.forall_mem_cons.2 ⟨subd3_1_109, List.forall_mem_cons.2 ⟨subd3_1_110, List.forall_mem_cons.2 ⟨subd3_1_111, List.forall_mem_cons.2 ⟨subd3_1_112, List.forall_mem_cons.2 ⟨subd3_1_113, List.forall_mem_cons.2 ⟨subd3_1_114, List.forall_mem_cons.2 ⟨subd3_1_115, List.forall_mem_cons.2 ⟨subd3_1_116, List.forall_mem_cons.2 ⟨subd3_1_117, List.forall_mem_cons.2 ⟨subd3_1_118, List.forall_mem_cons.2 ⟨subd3_1_119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
