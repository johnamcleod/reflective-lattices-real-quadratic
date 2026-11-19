import ReflectZphi.Data.Cert5.C031.Base

namespace ReflectZphi.Data.Cert5.C031
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_32 : sub2 [-2, 3] = true := by decide +kernel
theorem sub2_33 : sub2 [-2, 4] = true := by decide +kernel
theorem sub2_34 : sub2 [-2, 5] = true := by decide +kernel
theorem sub2_35 : sub2 [-2, 6] = true := by decide +kernel
theorem sub2_36 : sub2 [-1, -7] = true := by decide +kernel
theorem sub2_37 : sub2 [-1, -6] = true := by decide +kernel
theorem sub2_38 : sub2 [-1, -5] = true := by decide +kernel
theorem sub2_39 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_40 : sub2 [-1, -3] = true := by decide +kernel
theorem sub2_41 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_42 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_43 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_44 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_45 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_46 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_47 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_48 : sub2 [-1, 5] = true := by decide +kernel
theorem sub2_49 : sub2 [-1, 6] = true := by decide +kernel
theorem sub2_50 : sub2 [0, -7] = true := by decide +kernel
theorem sub2_51 : sub2 [0, -6] = true := by decide +kernel
theorem sub2_52 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_53 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_54 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_55 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_56 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_57 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_58 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_59 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_60 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_61 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_62 : sub2 [0, 5] = true := by decide +kernel
theorem sub2_63 : sub2 [0, 6] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_64 : sub2 [1, -7] = true := by decide +kernel
theorem sub2_65 : sub2 [1, -6] = true := by decide +kernel
theorem sub2_66 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_67 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_68 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_69 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_70 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_71 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_72 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_73 : sub2 [1, 2] = true := by decide +kernel
theorem sub2_74 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_75 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_76 : sub2 [1, 5] = true := by decide +kernel
theorem sub2_77 : sub2 [1, 6] = true := by decide +kernel
theorem sub2_78 : sub2 [2, -7] = true := by decide +kernel
theorem sub2_79 : sub2 [2, -6] = true := by decide +kernel
theorem sub2_80 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_81 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_82 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_83 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_84 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_85 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_86 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_87 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_88 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_89 : sub2 [2, 4] = true := by decide +kernel
theorem sub2_90 : sub2 [2, 5] = true := by decide +kernel
theorem sub2_91 : sub2 [3, -7] = true := by decide +kernel
theorem sub2_92 : sub2 [3, -6] = true := by decide +kernel
theorem sub2_93 : sub2 [3, -5] = true := by decide +kernel
theorem sub2_94 : sub2 [3, -4] = true := by decide +kernel
theorem sub2_95 : sub2 [3, -3] = true := by decide +kernel
theorem sb2_2 : ∀ q ∈ blk2_2, sub2 q = true := by
  unfold blk2_2
  exact List.forall_mem_cons.2 ⟨sub2_64, List.forall_mem_cons.2 ⟨sub2_65, List.forall_mem_cons.2 ⟨sub2_66, List.forall_mem_cons.2 ⟨sub2_67, List.forall_mem_cons.2 ⟨sub2_68, List.forall_mem_cons.2 ⟨sub2_69, List.forall_mem_cons.2 ⟨sub2_70, List.forall_mem_cons.2 ⟨sub2_71, List.forall_mem_cons.2 ⟨sub2_72, List.forall_mem_cons.2 ⟨sub2_73, List.forall_mem_cons.2 ⟨sub2_74, List.forall_mem_cons.2 ⟨sub2_75, List.forall_mem_cons.2 ⟨sub2_76, List.forall_mem_cons.2 ⟨sub2_77, List.forall_mem_cons.2 ⟨sub2_78, List.forall_mem_cons.2 ⟨sub2_79, List.forall_mem_cons.2 ⟨sub2_80, List.forall_mem_cons.2 ⟨sub2_81, List.forall_mem_cons.2 ⟨sub2_82, List.forall_mem_cons.2 ⟨sub2_83, List.forall_mem_cons.2 ⟨sub2_84, List.forall_mem_cons.2 ⟨sub2_85, List.forall_mem_cons.2 ⟨sub2_86, List.forall_mem_cons.2 ⟨sub2_87, List.forall_mem_cons.2 ⟨sub2_88, List.forall_mem_cons.2 ⟨sub2_89, List.forall_mem_cons.2 ⟨sub2_90, List.forall_mem_cons.2 ⟨sub2_91, List.forall_mem_cons.2 ⟨sub2_92, List.forall_mem_cons.2 ⟨sub2_93, List.forall_mem_cons.2 ⟨sub2_94, List.forall_mem_cons.2 ⟨sub2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_96 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_97 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_98 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_99 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_100 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_101 : sub2 [3, 3] = true := by decide +kernel
theorem sub2_102 : sub2 [3, 4] = true := by decide +kernel
theorem sub2_103 : sub2 [4, -6] = true := by decide +kernel
theorem sub2_104 : sub2 [4, -5] = true := by decide +kernel
theorem sub2_105 : sub2 [4, -4] = true := by decide +kernel
theorem sub2_106 : sub2 [4, -3] = true := by decide +kernel
theorem sub2_107 : sub2 [4, -2] = true := by decide +kernel
theorem sub2_108 : sub2 [4, -1] = true := by decide +kernel
theorem sub2_109 : sub2 [4, 0] = true := by decide +kernel
theorem sub2_110 : sub2 [4, 1] = true := by decide +kernel
theorem sub2_111 : sub2 [4, 2] = true := by decide +kernel
theorem sub2_112 : sub2 [4, 3] = true := by decide +kernel
theorem sub2_113 : sub2 [5] = true := by decide +kernel
theorem sb2_3 : ∀ q ∈ blk2_3, sub2 q = true := by
  unfold blk2_3
  exact List.forall_mem_cons.2 ⟨sub2_96, List.forall_mem_cons.2 ⟨sub2_97, List.forall_mem_cons.2 ⟨sub2_98, List.forall_mem_cons.2 ⟨sub2_99, List.forall_mem_cons.2 ⟨sub2_100, List.forall_mem_cons.2 ⟨sub2_101, List.forall_mem_cons.2 ⟨sub2_102, List.forall_mem_cons.2 ⟨sub2_103, List.forall_mem_cons.2 ⟨sub2_104, List.forall_mem_cons.2 ⟨sub2_105, List.forall_mem_cons.2 ⟨sub2_106, List.forall_mem_cons.2 ⟨sub2_107, List.forall_mem_cons.2 ⟨sub2_108, List.forall_mem_cons.2 ⟨sub2_109, List.forall_mem_cons.2 ⟨sub2_110, List.forall_mem_cons.2 ⟨sub2_111, List.forall_mem_cons.2 ⟨sub2_112, List.forall_mem_cons.2 ⟨sub2_113, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C031
