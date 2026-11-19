import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_32 : subd9_3 [-3, -2] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [-3, -1] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [-3, 0] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [-3, 1] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [-3, 2] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [-3, 3] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [-2, -7] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [-2, -6] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [-2, -4] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [-2, 3] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [-2, 4] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [-1, -6] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [-1, 4] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [-1, 5] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [0, -6] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [0, -5] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [0, 4] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [0, 5] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [1, -6] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [1, 4] = true := by decide +kernel
theorem subd9_3_85 : subd9_3 [1, 5] = true := by decide +kernel
theorem subd9_3_86 : subd9_3 [2, -5] = true := by decide +kernel
theorem subd9_3_87 : subd9_3 [2, -4] = true := by decide +kernel
theorem subd9_3_88 : subd9_3 [2, -3] = true := by decide +kernel
theorem subd9_3_89 : subd9_3 [2, -2] = true := by decide +kernel
theorem subd9_3_90 : subd9_3 [2, -1] = true := by decide +kernel
theorem subd9_3_91 : subd9_3 [2, 0] = true := by decide +kernel
theorem subd9_3_92 : subd9_3 [2, 1] = true := by decide +kernel
theorem subd9_3_93 : subd9_3 [2, 2] = true := by decide +kernel
theorem subd9_3_94 : subd9_3 [2, 3] = true := by decide +kernel
theorem subd9_3_95 : subd9_3 [2, 4] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_cons.2 ⟨subd9_3_85, List.forall_mem_cons.2 ⟨subd9_3_86, List.forall_mem_cons.2 ⟨subd9_3_87, List.forall_mem_cons.2 ⟨subd9_3_88, List.forall_mem_cons.2 ⟨subd9_3_89, List.forall_mem_cons.2 ⟨subd9_3_90, List.forall_mem_cons.2 ⟨subd9_3_91, List.forall_mem_cons.2 ⟨subd9_3_92, List.forall_mem_cons.2 ⟨subd9_3_93, List.forall_mem_cons.2 ⟨subd9_3_94, List.forall_mem_cons.2 ⟨subd9_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
