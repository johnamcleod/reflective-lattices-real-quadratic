import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_32 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [-2, 3] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [-2, 4] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [-2, 5] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [-1, -7] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [-1, -6] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_46 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_47 : subd6_3 [-1, 4] = true := by decide +kernel
theorem subd6_3_48 : subd6_3 [-1, 5] = true := by decide +kernel
theorem subd6_3_49 : subd6_3 [0, -7] = true := by decide +kernel
theorem subd6_3_50 : subd6_3 [0, -6] = true := by decide +kernel
theorem subd6_3_51 : subd6_3 [0, -5] = true := by decide +kernel
theorem subd6_3_52 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_53 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_54 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_55 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_56 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_57 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_58 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_59 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_60 : subd6_3 [0, 4] = true := by decide +kernel
theorem subd6_3_61 : subd6_3 [0, 5] = true := by decide +kernel
theorem subd6_3_62 : subd6_3 [0, 6] = true := by decide +kernel
theorem subd6_3_63 : subd6_3 [1, -6] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_cons.2 ⟨subd6_3_46, List.forall_mem_cons.2 ⟨subd6_3_47, List.forall_mem_cons.2 ⟨subd6_3_48, List.forall_mem_cons.2 ⟨subd6_3_49, List.forall_mem_cons.2 ⟨subd6_3_50, List.forall_mem_cons.2 ⟨subd6_3_51, List.forall_mem_cons.2 ⟨subd6_3_52, List.forall_mem_cons.2 ⟨subd6_3_53, List.forall_mem_cons.2 ⟨subd6_3_54, List.forall_mem_cons.2 ⟨subd6_3_55, List.forall_mem_cons.2 ⟨subd6_3_56, List.forall_mem_cons.2 ⟨subd6_3_57, List.forall_mem_cons.2 ⟨subd6_3_58, List.forall_mem_cons.2 ⟨subd6_3_59, List.forall_mem_cons.2 ⟨subd6_3_60, List.forall_mem_cons.2 ⟨subd6_3_61, List.forall_mem_cons.2 ⟨subd6_3_62, List.forall_mem_cons.2 ⟨subd6_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_64 : subd6_3 [1, -5] = true := by decide +kernel
theorem subd6_3_65 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_66 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_67 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_68 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_69 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_70 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_71 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_72 : subd6_3 [1, 3] = true := by decide +kernel
theorem subd6_3_73 : subd6_3 [1, 4] = true := by decide +kernel
theorem subd6_3_74 : subd6_3 [1, 5] = true := by decide +kernel
theorem subd6_3_75 : subd6_3 [1, 6] = true := by decide +kernel
theorem subd6_3_76 : subd6_3 [2, -6] = true := by decide +kernel
theorem subd6_3_77 : subd6_3 [2, -5] = true := by decide +kernel
theorem subd6_3_78 : subd6_3 [2, -4] = true := by decide +kernel
theorem subd6_3_79 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_80 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_81 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_82 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_83 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_84 : subd6_3 [2, 2] = true := by decide +kernel
theorem subd6_3_85 : subd6_3 [2, 3] = true := by decide +kernel
theorem subd6_3_86 : subd6_3 [2, 4] = true := by decide +kernel
theorem subd6_3_87 : subd6_3 [2, 5] = true := by decide +kernel
theorem subd6_3_88 : subd6_3 [2, 6] = true := by decide +kernel
theorem subd6_3_89 : subd6_3 [3, -5] = true := by decide +kernel
theorem subd6_3_90 : subd6_3 [3, -4] = true := by decide +kernel
theorem subd6_3_91 : subd6_3 [3, -3] = true := by decide +kernel
theorem subd6_3_92 : subd6_3 [3, -2] = true := by decide +kernel
theorem subd6_3_93 : subd6_3 [3, -1] = true := by decide +kernel
theorem subd6_3_94 : subd6_3 [3, 0] = true := by decide +kernel
theorem subd6_3_95 : subd6_3 [3, 1] = true := by decide +kernel
theorem sbd6_3_2 : ∀ q ∈ blkd6_3_2, subd6_3 q = true := by
  unfold blkd6_3_2
  exact List.forall_mem_cons.2 ⟨subd6_3_64, List.forall_mem_cons.2 ⟨subd6_3_65, List.forall_mem_cons.2 ⟨subd6_3_66, List.forall_mem_cons.2 ⟨subd6_3_67, List.forall_mem_cons.2 ⟨subd6_3_68, List.forall_mem_cons.2 ⟨subd6_3_69, List.forall_mem_cons.2 ⟨subd6_3_70, List.forall_mem_cons.2 ⟨subd6_3_71, List.forall_mem_cons.2 ⟨subd6_3_72, List.forall_mem_cons.2 ⟨subd6_3_73, List.forall_mem_cons.2 ⟨subd6_3_74, List.forall_mem_cons.2 ⟨subd6_3_75, List.forall_mem_cons.2 ⟨subd6_3_76, List.forall_mem_cons.2 ⟨subd6_3_77, List.forall_mem_cons.2 ⟨subd6_3_78, List.forall_mem_cons.2 ⟨subd6_3_79, List.forall_mem_cons.2 ⟨subd6_3_80, List.forall_mem_cons.2 ⟨subd6_3_81, List.forall_mem_cons.2 ⟨subd6_3_82, List.forall_mem_cons.2 ⟨subd6_3_83, List.forall_mem_cons.2 ⟨subd6_3_84, List.forall_mem_cons.2 ⟨subd6_3_85, List.forall_mem_cons.2 ⟨subd6_3_86, List.forall_mem_cons.2 ⟨subd6_3_87, List.forall_mem_cons.2 ⟨subd6_3_88, List.forall_mem_cons.2 ⟨subd6_3_89, List.forall_mem_cons.2 ⟨subd6_3_90, List.forall_mem_cons.2 ⟨subd6_3_91, List.forall_mem_cons.2 ⟨subd6_3_92, List.forall_mem_cons.2 ⟨subd6_3_93, List.forall_mem_cons.2 ⟨subd6_3_94, List.forall_mem_cons.2 ⟨subd6_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_96 : subd6_3 [3, 2] = true := by decide +kernel
theorem subd6_3_97 : subd6_3 [3, 3] = true := by decide +kernel
theorem subd6_3_98 : subd6_3 [3, 4] = true := by decide +kernel
theorem subd6_3_99 : subd6_3 [3, 5] = true := by decide +kernel
theorem subd6_3_100 : subd6_3 [3, 6] = true := by decide +kernel
theorem subd6_3_101 : subd6_3 [4, -3] = true := by decide +kernel
theorem subd6_3_102 : subd6_3 [4, -2] = true := by decide +kernel
theorem subd6_3_103 : subd6_3 [4, -1] = true := by decide +kernel
theorem subd6_3_104 : subd6_3 [4, 0] = true := by decide +kernel
theorem subd6_3_105 : subd6_3 [4, 1] = true := by decide +kernel
theorem subd6_3_106 : subd6_3 [4, 2] = true := by decide +kernel
theorem subd6_3_107 : subd6_3 [4, 3] = true := by decide +kernel
theorem subd6_3_108 : subd6_3 [4, 4] = true := by decide +kernel
theorem subd6_3_109 : subd6_3 [4, 5] = true := by decide +kernel
theorem subd6_3_110 : subd6_3 [4, 6] = true := by decide +kernel
theorem subd6_3_111 : subd6_3 [5] = true := by decide +kernel
theorem sbd6_3_3 : ∀ q ∈ blkd6_3_3, subd6_3 q = true := by
  unfold blkd6_3_3
  exact List.forall_mem_cons.2 ⟨subd6_3_96, List.forall_mem_cons.2 ⟨subd6_3_97, List.forall_mem_cons.2 ⟨subd6_3_98, List.forall_mem_cons.2 ⟨subd6_3_99, List.forall_mem_cons.2 ⟨subd6_3_100, List.forall_mem_cons.2 ⟨subd6_3_101, List.forall_mem_cons.2 ⟨subd6_3_102, List.forall_mem_cons.2 ⟨subd6_3_103, List.forall_mem_cons.2 ⟨subd6_3_104, List.forall_mem_cons.2 ⟨subd6_3_105, List.forall_mem_cons.2 ⟨subd6_3_106, List.forall_mem_cons.2 ⟨subd6_3_107, List.forall_mem_cons.2 ⟨subd6_3_108, List.forall_mem_cons.2 ⟨subd6_3_109, List.forall_mem_cons.2 ⟨subd6_3_110, List.forall_mem_cons.2 ⟨subd6_3_111, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
