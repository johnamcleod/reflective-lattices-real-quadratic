import ReflectZphi.Data.Cert5.C054.Base

namespace ReflectZphi.Data.Cert5.C054
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_64 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_65 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_66 : sub4 [2, -7] = true := by decide +kernel
theorem sub4_67 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_68 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_69 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_70 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_71 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_72 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_73 : sub4 [2, 0] = true := by decide +kernel
theorem sub4_74 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_75 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_76 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_77 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_78 : sub4 [3, -7] = true := by decide +kernel
theorem sub4_79 : sub4 [3, -6] = true := by decide +kernel
theorem sub4_80 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_81 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_82 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_83 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_84 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_85 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_86 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_87 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_88 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_89 : sub4 [4, -6] = true := by decide +kernel
theorem sub4_90 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_91 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_92 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_93 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_94 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_95 : sub4 [4, 0] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_97 : sub4 [5] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_nil _⟩⟩

end ReflectZphi.Data.Cert5.C054
