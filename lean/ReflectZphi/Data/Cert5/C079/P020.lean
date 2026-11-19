import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_32 : sub8 [-1, -1] = true := by decide +kernel
theorem sub8_33 : sub8 [-1, 0] = true := by decide +kernel
theorem sub8_34 : sub8 [-1, 1] = true := by decide +kernel
theorem sub8_35 : sub8 [-1, 2] = true := by decide +kernel
theorem sub8_36 : sub8 [-1, 3] = true := by decide +kernel
theorem sub8_37 : sub8 [-1, 4] = true := by decide +kernel
theorem sub8_38 : sub8 [-1, 5] = true := by decide +kernel
theorem sub8_39 : sub8 [0, -5] = true := by decide +kernel
theorem sub8_40 : sub8 [0, -4] = true := by decide +kernel
theorem sub8_41 : sub8 [0, -3] = true := by decide +kernel
theorem sub8_42 : sub8 [0, -2] = true := by decide +kernel
theorem sub8_43 : sub8 [0, -1] = true := by decide +kernel
theorem sub8_44 : sub8 [0, 0, -7] = true := by decide +kernel
theorem sub8_45 : sub8 [0, 0, -6] = true := by decide +kernel
theorem sub8_46 : sub8 [0, 0, -5] = true := by decide +kernel
theorem sub8_47 : sub8 [0, 0, -4] = true := by decide +kernel
theorem sub8_48 : sub8 [0, 0, -3] = true := by decide +kernel
theorem sub8_49 : sub8 [0, 0, -2] = true := by decide +kernel
theorem sub8_50 : sub8 [0, 0, -1] = true := by decide +kernel
theorem sub8_51 : sub8 [0, 0, 0] = true := by decide +kernel
theorem sub8_52 : sub8 [0, 0, 1] = true := by decide +kernel
theorem sub8_53 : sub8 [0, 0, 2] = true := by decide +kernel
theorem sub8_54 : sub8 [0, 0, 3] = true := by decide +kernel
theorem sub8_55 : sub8 [0, 0, 4] = true := by decide +kernel
theorem sub8_56 : sub8 [0, 0, 5] = true := by decide +kernel
theorem sub8_57 : sub8 [0, 0, 6] = true := by decide +kernel
theorem sub8_58 : sub8 [0, 1] = true := by decide +kernel
theorem sub8_59 : sub8 [0, 2] = true := by decide +kernel
theorem sub8_60 : sub8 [0, 3] = true := by decide +kernel
theorem sub8_61 : sub8 [0, 4] = true := by decide +kernel
theorem sub8_62 : sub8 [1, -6] = true := by decide +kernel
theorem sub8_63 : sub8 [1, -5] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [1, -4] = true := by decide +kernel
theorem sub8_65 : sub8 [1, -3] = true := by decide +kernel
theorem sub8_66 : sub8 [1, -2] = true := by decide +kernel
theorem sub8_67 : sub8 [1, -1] = true := by decide +kernel
theorem sub8_68 : sub8 [1, 0] = true := by decide +kernel
theorem sub8_69 : sub8 [1, 1] = true := by decide +kernel
theorem sub8_70 : sub8 [1, 2] = true := by decide +kernel
theorem sub8_71 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_72 : sub8 [1, 4] = true := by decide +kernel
theorem sub8_73 : sub8 [2, -5] = true := by decide +kernel
theorem sub8_74 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_75 : sub8 [2, -3] = true := by decide +kernel
theorem sub8_76 : sub8 [2, -2] = true := by decide +kernel
theorem sub8_77 : sub8 [2, -1] = true := by decide +kernel
theorem sub8_78 : sub8 [2, 0] = true := by decide +kernel
theorem sub8_79 : sub8 [2, 1] = true := by decide +kernel
theorem sub8_80 : sub8 [2, 2] = true := by decide +kernel
theorem sub8_81 : sub8 [2, 3] = true := by decide +kernel
theorem sub8_82 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_83 : sub8 [3, -5] = true := by decide +kernel
theorem sub8_84 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_85 : sub8 [3, -3] = true := by decide +kernel
theorem sub8_86 : sub8 [3, -2] = true := by decide +kernel
theorem sub8_87 : sub8 [3, -1] = true := by decide +kernel
theorem sub8_88 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_89 : sub8 [3, 1] = true := by decide +kernel
theorem sub8_90 : sub8 [3, 2] = true := by decide +kernel
theorem sub8_91 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_92 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_93 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_94 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_95 : sub8 [4, -2] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [4, -1] = true := by decide +kernel
theorem sub8_97 : sub8 [4, 0] = true := by decide +kernel
theorem sub8_98 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_99 : sub8 [4, 2] = true := by decide +kernel
theorem sub8_100 : sub8 [5] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
