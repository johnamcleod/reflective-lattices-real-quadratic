import ReflectZphi.Data.Cert5.C056.Base

namespace ReflectZphi.Data.Cert5.C056
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_64 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_65 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_66 : sub6 [1, 5] = true := by decide +kernel
theorem sub6_67 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_68 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_69 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_70 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_71 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_72 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_73 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_74 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_75 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_76 : sub6 [2, 5] = true := by decide +kernel
theorem sub6_77 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_78 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_79 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_80 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_81 : sub6 [3, 1] = true := by decide +kernel
theorem sub6_82 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_83 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_84 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_85 : sub6 [3, 5] = true := by decide +kernel
theorem sub6_86 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_87 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_88 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_89 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_90 : sub6 [4, 2] = true := by decide +kernel
theorem sub6_91 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_92 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_93 : sub6 [4, 5] = true := by decide +kernel
theorem sub6_94 : sub6 [5, -1] = true := by decide +kernel
theorem sub6_95 : sub6 [5, 0] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [5, 1] = true := by decide +kernel
theorem sub6_97 : sub6 [5, 2] = true := by decide +kernel
theorem sub6_98 : sub6 [5, 3] = true := by decide +kernel
theorem sub6_99 : sub6 [5, 4] = true := by decide +kernel
theorem sub6_100 : sub6 [5, 5] = true := by decide +kernel
theorem sub6_101 : sub6 [6] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-3] = true := by decide +kernel
theorem sub7_1 : sub7 [-2] = true := by decide +kernel
theorem sub7_2 : sub7 [-1, -3] = true := by decide +kernel
theorem sub7_3 : sub7 [-1, -2] = true := by decide +kernel
theorem sub7_4 : sub7 [-1, -1] = true := by decide +kernel
theorem sub7_5 : sub7 [-1, 0] = true := by decide +kernel
theorem sub7_6 : sub7 [-1, 1] = true := by decide +kernel
theorem sub7_7 : sub7 [-1, 2] = true := by decide +kernel
theorem sub7_8 : sub7 [-1, 3] = true := by decide +kernel
theorem sub7_9 : sub7 [0, -4] = true := by decide +kernel
theorem sub7_10 : sub7 [0, -3] = true := by decide +kernel
theorem sub7_11 : sub7 [0, -2] = true := by decide +kernel
theorem sub7_12 : sub7 [0, -1] = true := by decide +kernel
theorem sub7_13 : sub7 [0, 0] = true := by decide +kernel
theorem sub7_14 : sub7 [0, 1] = true := by decide +kernel
theorem sub7_15 : sub7 [0, 2] = true := by decide +kernel
theorem sub7_16 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_17 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_18 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_19 : sub7 [1, -2] = true := by decide +kernel
theorem sub7_20 : sub7 [1, -1] = true := by decide +kernel
theorem sub7_21 : sub7 [1, 0] = true := by decide +kernel
theorem sub7_22 : sub7 [1, 1] = true := by decide +kernel
theorem sub7_23 : sub7 [1, 2] = true := by decide +kernel
theorem sub7_24 : sub7 [2] = true := by decide +kernel
theorem sub7_25 : sub7 [3] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C056
