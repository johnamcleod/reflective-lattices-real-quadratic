import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_6_32 : subd3_6 [-2, 4] = true := by decide +kernel
theorem subd3_6_33 : subd3_6 [-2, 5] = true := by decide +kernel
theorem subd3_6_34 : subd3_6 [-2, 6] = true := by decide +kernel
theorem subd3_6_35 : subd3_6 [-1, -6] = true := by decide +kernel
theorem subd3_6_36 : subd3_6 [-1, -5] = true := by decide +kernel
theorem subd3_6_37 : subd3_6 [-1, -4] = true := by decide +kernel
theorem subd3_6_38 : subd3_6 [-1, -3] = true := by decide +kernel
theorem subd3_6_39 : subd3_6 [-1, -2] = true := by decide +kernel
theorem subd3_6_40 : subd3_6 [-1, -1] = true := by decide +kernel
theorem subd3_6_41 : subd3_6 [-1, 0] = true := by decide +kernel
theorem subd3_6_42 : subd3_6 [-1, 1] = true := by decide +kernel
theorem subd3_6_43 : subd3_6 [-1, 2] = true := by decide +kernel
theorem subd3_6_44 : subd3_6 [-1, 3] = true := by decide +kernel
theorem subd3_6_45 : subd3_6 [-1, 4] = true := by decide +kernel
theorem subd3_6_46 : subd3_6 [-1, 5] = true := by decide +kernel
theorem subd3_6_47 : subd3_6 [-1, 6] = true := by decide +kernel
theorem subd3_6_48 : subd3_6 [0, -7] = true := by decide +kernel
theorem subd3_6_49 : subd3_6 [0, -6] = true := by decide +kernel
theorem subd3_6_50 : subd3_6 [0, -5] = true := by decide +kernel
theorem subd3_6_51 : subd3_6 [0, -4] = true := by decide +kernel
theorem subd3_6_52 : subd3_6 [0, -3] = true := by decide +kernel
theorem subd3_6_53 : subd3_6 [0, -2] = true := by decide +kernel
theorem subd3_6_54 : subd3_6 [0, -1] = true := by decide +kernel
theorem subd3_6_55 : subd3_6 [0, 0] = true := by decide +kernel
theorem subd3_6_56 : subd3_6 [0, 1] = true := by decide +kernel
theorem subd3_6_57 : subd3_6 [0, 2] = true := by decide +kernel
theorem subd3_6_58 : subd3_6 [0, 3] = true := by decide +kernel
theorem subd3_6_59 : subd3_6 [0, 4] = true := by decide +kernel
theorem subd3_6_60 : subd3_6 [0, 5] = true := by decide +kernel
theorem subd3_6_61 : subd3_6 [0, 6] = true := by decide +kernel
theorem subd3_6_62 : subd3_6 [1, -7] = true := by decide +kernel
theorem subd3_6_63 : subd3_6 [1, -6] = true := by decide +kernel
theorem sbd3_6_1 : ∀ q ∈ blkd3_6_1, subd3_6 q = true := by
  unfold blkd3_6_1
  exact List.forall_mem_cons.2 ⟨subd3_6_32, List.forall_mem_cons.2 ⟨subd3_6_33, List.forall_mem_cons.2 ⟨subd3_6_34, List.forall_mem_cons.2 ⟨subd3_6_35, List.forall_mem_cons.2 ⟨subd3_6_36, List.forall_mem_cons.2 ⟨subd3_6_37, List.forall_mem_cons.2 ⟨subd3_6_38, List.forall_mem_cons.2 ⟨subd3_6_39, List.forall_mem_cons.2 ⟨subd3_6_40, List.forall_mem_cons.2 ⟨subd3_6_41, List.forall_mem_cons.2 ⟨subd3_6_42, List.forall_mem_cons.2 ⟨subd3_6_43, List.forall_mem_cons.2 ⟨subd3_6_44, List.forall_mem_cons.2 ⟨subd3_6_45, List.forall_mem_cons.2 ⟨subd3_6_46, List.forall_mem_cons.2 ⟨subd3_6_47, List.forall_mem_cons.2 ⟨subd3_6_48, List.forall_mem_cons.2 ⟨subd3_6_49, List.forall_mem_cons.2 ⟨subd3_6_50, List.forall_mem_cons.2 ⟨subd3_6_51, List.forall_mem_cons.2 ⟨subd3_6_52, List.forall_mem_cons.2 ⟨subd3_6_53, List.forall_mem_cons.2 ⟨subd3_6_54, List.forall_mem_cons.2 ⟨subd3_6_55, List.forall_mem_cons.2 ⟨subd3_6_56, List.forall_mem_cons.2 ⟨subd3_6_57, List.forall_mem_cons.2 ⟨subd3_6_58, List.forall_mem_cons.2 ⟨subd3_6_59, List.forall_mem_cons.2 ⟨subd3_6_60, List.forall_mem_cons.2 ⟨subd3_6_61, List.forall_mem_cons.2 ⟨subd3_6_62, List.forall_mem_cons.2 ⟨subd3_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_64 : subd3_6 [1, -5] = true := by decide +kernel
theorem subd3_6_65 : subd3_6 [1, -4] = true := by decide +kernel
theorem subd3_6_66 : subd3_6 [1, -3] = true := by decide +kernel
theorem subd3_6_67 : subd3_6 [1, -2] = true := by decide +kernel
theorem subd3_6_68 : subd3_6 [1, -1] = true := by decide +kernel
theorem subd3_6_69 : subd3_6 [1, 0] = true := by decide +kernel
theorem subd3_6_70 : subd3_6 [1, 1] = true := by decide +kernel
theorem subd3_6_71 : subd3_6 [1, 2] = true := by decide +kernel
theorem subd3_6_72 : subd3_6 [1, 3] = true := by decide +kernel
theorem subd3_6_73 : subd3_6 [1, 4] = true := by decide +kernel
theorem subd3_6_74 : subd3_6 [1, 5] = true := by decide +kernel
theorem subd3_6_75 : subd3_6 [2, -7] = true := by decide +kernel
theorem subd3_6_76 : subd3_6 [2, -6] = true := by decide +kernel
theorem subd3_6_77 : subd3_6 [2, -5] = true := by decide +kernel
theorem subd3_6_78 : subd3_6 [2, -4] = true := by decide +kernel
theorem subd3_6_79 : subd3_6 [2, -3] = true := by decide +kernel
theorem subd3_6_80 : subd3_6 [2, -2] = true := by decide +kernel
theorem subd3_6_81 : subd3_6 [2, -1] = true := by decide +kernel
theorem subd3_6_82 : subd3_6 [2, 0] = true := by decide +kernel
theorem subd3_6_83 : subd3_6 [2, 1] = true := by decide +kernel
theorem subd3_6_84 : subd3_6 [2, 2] = true := by decide +kernel
theorem subd3_6_85 : subd3_6 [2, 3] = true := by decide +kernel
theorem subd3_6_86 : subd3_6 [2, 4] = true := by decide +kernel
theorem subd3_6_87 : subd3_6 [2, 5] = true := by decide +kernel
theorem subd3_6_88 : subd3_6 [3, -7] = true := by decide +kernel
theorem subd3_6_89 : subd3_6 [3, -6] = true := by decide +kernel
theorem subd3_6_90 : subd3_6 [3, -5] = true := by decide +kernel
theorem subd3_6_91 : subd3_6 [3, -4] = true := by decide +kernel
theorem subd3_6_92 : subd3_6 [3, -3] = true := by decide +kernel
theorem subd3_6_93 : subd3_6 [3, -2] = true := by decide +kernel
theorem subd3_6_94 : subd3_6 [3, -1] = true := by decide +kernel
theorem subd3_6_95 : subd3_6 [3, 0] = true := by decide +kernel
theorem sbd3_6_2 : ∀ q ∈ blkd3_6_2, subd3_6 q = true := by
  unfold blkd3_6_2
  exact List.forall_mem_cons.2 ⟨subd3_6_64, List.forall_mem_cons.2 ⟨subd3_6_65, List.forall_mem_cons.2 ⟨subd3_6_66, List.forall_mem_cons.2 ⟨subd3_6_67, List.forall_mem_cons.2 ⟨subd3_6_68, List.forall_mem_cons.2 ⟨subd3_6_69, List.forall_mem_cons.2 ⟨subd3_6_70, List.forall_mem_cons.2 ⟨subd3_6_71, List.forall_mem_cons.2 ⟨subd3_6_72, List.forall_mem_cons.2 ⟨subd3_6_73, List.forall_mem_cons.2 ⟨subd3_6_74, List.forall_mem_cons.2 ⟨subd3_6_75, List.forall_mem_cons.2 ⟨subd3_6_76, List.forall_mem_cons.2 ⟨subd3_6_77, List.forall_mem_cons.2 ⟨subd3_6_78, List.forall_mem_cons.2 ⟨subd3_6_79, List.forall_mem_cons.2 ⟨subd3_6_80, List.forall_mem_cons.2 ⟨subd3_6_81, List.forall_mem_cons.2 ⟨subd3_6_82, List.forall_mem_cons.2 ⟨subd3_6_83, List.forall_mem_cons.2 ⟨subd3_6_84, List.forall_mem_cons.2 ⟨subd3_6_85, List.forall_mem_cons.2 ⟨subd3_6_86, List.forall_mem_cons.2 ⟨subd3_6_87, List.forall_mem_cons.2 ⟨subd3_6_88, List.forall_mem_cons.2 ⟨subd3_6_89, List.forall_mem_cons.2 ⟨subd3_6_90, List.forall_mem_cons.2 ⟨subd3_6_91, List.forall_mem_cons.2 ⟨subd3_6_92, List.forall_mem_cons.2 ⟨subd3_6_93, List.forall_mem_cons.2 ⟨subd3_6_94, List.forall_mem_cons.2 ⟨subd3_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_6_96 : subd3_6 [3, 1] = true := by decide +kernel
theorem subd3_6_97 : subd3_6 [3, 2] = true := by decide +kernel
theorem subd3_6_98 : subd3_6 [3, 3] = true := by decide +kernel
theorem subd3_6_99 : subd3_6 [3, 4] = true := by decide +kernel
theorem subd3_6_100 : subd3_6 [4, -6] = true := by decide +kernel
theorem subd3_6_101 : subd3_6 [4, -5] = true := by decide +kernel
theorem subd3_6_102 : subd3_6 [4, -4] = true := by decide +kernel
theorem subd3_6_103 : subd3_6 [4, -3] = true := by decide +kernel
theorem subd3_6_104 : subd3_6 [4, -2] = true := by decide +kernel
theorem subd3_6_105 : subd3_6 [4, -1] = true := by decide +kernel
theorem subd3_6_106 : subd3_6 [4, 0] = true := by decide +kernel
theorem subd3_6_107 : subd3_6 [4, 1] = true := by decide +kernel
theorem subd3_6_108 : subd3_6 [4, 2] = true := by decide +kernel
theorem subd3_6_109 : subd3_6 [5] = true := by decide +kernel
theorem sbd3_6_3 : ∀ q ∈ blkd3_6_3, subd3_6 q = true := by
  unfold blkd3_6_3
  exact List.forall_mem_cons.2 ⟨subd3_6_96, List.forall_mem_cons.2 ⟨subd3_6_97, List.forall_mem_cons.2 ⟨subd3_6_98, List.forall_mem_cons.2 ⟨subd3_6_99, List.forall_mem_cons.2 ⟨subd3_6_100, List.forall_mem_cons.2 ⟨subd3_6_101, List.forall_mem_cons.2 ⟨subd3_6_102, List.forall_mem_cons.2 ⟨subd3_6_103, List.forall_mem_cons.2 ⟨subd3_6_104, List.forall_mem_cons.2 ⟨subd3_6_105, List.forall_mem_cons.2 ⟨subd3_6_106, List.forall_mem_cons.2 ⟨subd3_6_107, List.forall_mem_cons.2 ⟨subd3_6_108, List.forall_mem_cons.2 ⟨subd3_6_109, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [1] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C123
