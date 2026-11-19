import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_11_32 : subd6_11 [-3, 3] = true := by decide +kernel
theorem subd6_11_33 : subd6_11 [-3, 4] = true := by decide +kernel
theorem subd6_11_34 : subd6_11 [-3, 5] = true := by decide +kernel
theorem subd6_11_35 : subd6_11 [-3, 6] = true := by decide +kernel
theorem subd6_11_36 : subd6_11 [-2, -7] = true := by decide +kernel
theorem subd6_11_37 : subd6_11 [-2, -6] = true := by decide +kernel
theorem subd6_11_38 : subd6_11 [-2, -5] = true := by decide +kernel
theorem subd6_11_39 : subd6_11 [-2, -4] = true := by decide +kernel
theorem subd6_11_40 : subd6_11 [-2, -3] = true := by decide +kernel
theorem subd6_11_41 : subd6_11 [-2, -2] = true := by decide +kernel
theorem subd6_11_42 : subd6_11 [-2, -1] = true := by decide +kernel
theorem subd6_11_43 : subd6_11 [-2, 0] = true := by decide +kernel
theorem subd6_11_44 : subd6_11 [-2, 1] = true := by decide +kernel
theorem subd6_11_45 : subd6_11 [-2, 2] = true := by decide +kernel
theorem subd6_11_46 : subd6_11 [-2, 3] = true := by decide +kernel
theorem subd6_11_47 : subd6_11 [-2, 4] = true := by decide +kernel
theorem subd6_11_48 : subd6_11 [-2, 5] = true := by decide +kernel
theorem subd6_11_49 : subd6_11 [-2, 6] = true := by decide +kernel
theorem subd6_11_50 : subd6_11 [-1, -7] = true := by decide +kernel
theorem subd6_11_51 : subd6_11 [-1, -6] = true := by decide +kernel
theorem subd6_11_52 : subd6_11 [-1, -5] = true := by decide +kernel
theorem subd6_11_53 : subd6_11 [-1, -4] = true := by decide +kernel
theorem subd6_11_54 : subd6_11 [-1, -3] = true := by decide +kernel
theorem subd6_11_55 : subd6_11 [-1, -2] = true := by decide +kernel
theorem subd6_11_56 : subd6_11 [-1, -1] = true := by decide +kernel
theorem subd6_11_57 : subd6_11 [-1, 0] = true := by decide +kernel
theorem subd6_11_58 : subd6_11 [-1, 1] = true := by decide +kernel
theorem subd6_11_59 : subd6_11 [-1, 2] = true := by decide +kernel
theorem subd6_11_60 : subd6_11 [-1, 3] = true := by decide +kernel
theorem subd6_11_61 : subd6_11 [-1, 4] = true := by decide +kernel
theorem subd6_11_62 : subd6_11 [-1, 5] = true := by decide +kernel
theorem subd6_11_63 : subd6_11 [-1, 6] = true := by decide +kernel
theorem sbd6_11_1 : ∀ q ∈ blkd6_11_1, subd6_11 q = true := by
  unfold blkd6_11_1
  exact List.forall_mem_cons.2 ⟨subd6_11_32, List.forall_mem_cons.2 ⟨subd6_11_33, List.forall_mem_cons.2 ⟨subd6_11_34, List.forall_mem_cons.2 ⟨subd6_11_35, List.forall_mem_cons.2 ⟨subd6_11_36, List.forall_mem_cons.2 ⟨subd6_11_37, List.forall_mem_cons.2 ⟨subd6_11_38, List.forall_mem_cons.2 ⟨subd6_11_39, List.forall_mem_cons.2 ⟨subd6_11_40, List.forall_mem_cons.2 ⟨subd6_11_41, List.forall_mem_cons.2 ⟨subd6_11_42, List.forall_mem_cons.2 ⟨subd6_11_43, List.forall_mem_cons.2 ⟨subd6_11_44, List.forall_mem_cons.2 ⟨subd6_11_45, List.forall_mem_cons.2 ⟨subd6_11_46, List.forall_mem_cons.2 ⟨subd6_11_47, List.forall_mem_cons.2 ⟨subd6_11_48, List.forall_mem_cons.2 ⟨subd6_11_49, List.forall_mem_cons.2 ⟨subd6_11_50, List.forall_mem_cons.2 ⟨subd6_11_51, List.forall_mem_cons.2 ⟨subd6_11_52, List.forall_mem_cons.2 ⟨subd6_11_53, List.forall_mem_cons.2 ⟨subd6_11_54, List.forall_mem_cons.2 ⟨subd6_11_55, List.forall_mem_cons.2 ⟨subd6_11_56, List.forall_mem_cons.2 ⟨subd6_11_57, List.forall_mem_cons.2 ⟨subd6_11_58, List.forall_mem_cons.2 ⟨subd6_11_59, List.forall_mem_cons.2 ⟨subd6_11_60, List.forall_mem_cons.2 ⟨subd6_11_61, List.forall_mem_cons.2 ⟨subd6_11_62, List.forall_mem_cons.2 ⟨subd6_11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_11_64 : subd6_11 [0, -7] = true := by decide +kernel
theorem subd6_11_65 : subd6_11 [0, -6] = true := by decide +kernel
theorem subd6_11_66 : subd6_11 [0, -5] = true := by decide +kernel
theorem subd6_11_67 : subd6_11 [0, -4] = true := by decide +kernel
theorem subd6_11_68 : subd6_11 [0, -3] = true := by decide +kernel
theorem subd6_11_69 : subd6_11 [0, -2] = true := by decide +kernel
theorem subd6_11_70 : subd6_11 [0, -1] = true := by decide +kernel
theorem subd6_11_71 : subd6_11 [0, 0] = true := by decide +kernel
theorem subd6_11_72 : subd6_11 [0, 1] = true := by decide +kernel
theorem subd6_11_73 : subd6_11 [0, 2] = true := by decide +kernel
theorem subd6_11_74 : subd6_11 [0, 3] = true := by decide +kernel
theorem subd6_11_75 : subd6_11 [0, 4] = true := by decide +kernel
theorem subd6_11_76 : subd6_11 [0, 5] = true := by decide +kernel
theorem subd6_11_77 : subd6_11 [0, 6] = true := by decide +kernel
theorem subd6_11_78 : subd6_11 [1, -7] = true := by decide +kernel
theorem subd6_11_79 : subd6_11 [1, -6] = true := by decide +kernel
theorem subd6_11_80 : subd6_11 [1, -5] = true := by decide +kernel
theorem subd6_11_81 : subd6_11 [1, -4] = true := by decide +kernel
theorem subd6_11_82 : subd6_11 [1, -3] = true := by decide +kernel
theorem subd6_11_83 : subd6_11 [1, -2] = true := by decide +kernel
theorem subd6_11_84 : subd6_11 [1, -1] = true := by decide +kernel
theorem subd6_11_85 : subd6_11 [1, 0] = true := by decide +kernel
theorem subd6_11_86 : subd6_11 [1, 1] = true := by decide +kernel
theorem subd6_11_87 : subd6_11 [1, 2] = true := by decide +kernel
theorem subd6_11_88 : subd6_11 [1, 3] = true := by decide +kernel
theorem subd6_11_89 : subd6_11 [1, 4] = true := by decide +kernel
theorem subd6_11_90 : subd6_11 [1, 5] = true := by decide +kernel
theorem subd6_11_91 : subd6_11 [1, 6] = true := by decide +kernel
theorem subd6_11_92 : subd6_11 [2, -7] = true := by decide +kernel
theorem subd6_11_93 : subd6_11 [2, -6] = true := by decide +kernel
theorem subd6_11_94 : subd6_11 [2, -5] = true := by decide +kernel
theorem subd6_11_95 : subd6_11 [2, -4] = true := by decide +kernel
theorem sbd6_11_2 : ∀ q ∈ blkd6_11_2, subd6_11 q = true := by
  unfold blkd6_11_2
  exact List.forall_mem_cons.2 ⟨subd6_11_64, List.forall_mem_cons.2 ⟨subd6_11_65, List.forall_mem_cons.2 ⟨subd6_11_66, List.forall_mem_cons.2 ⟨subd6_11_67, List.forall_mem_cons.2 ⟨subd6_11_68, List.forall_mem_cons.2 ⟨subd6_11_69, List.forall_mem_cons.2 ⟨subd6_11_70, List.forall_mem_cons.2 ⟨subd6_11_71, List.forall_mem_cons.2 ⟨subd6_11_72, List.forall_mem_cons.2 ⟨subd6_11_73, List.forall_mem_cons.2 ⟨subd6_11_74, List.forall_mem_cons.2 ⟨subd6_11_75, List.forall_mem_cons.2 ⟨subd6_11_76, List.forall_mem_cons.2 ⟨subd6_11_77, List.forall_mem_cons.2 ⟨subd6_11_78, List.forall_mem_cons.2 ⟨subd6_11_79, List.forall_mem_cons.2 ⟨subd6_11_80, List.forall_mem_cons.2 ⟨subd6_11_81, List.forall_mem_cons.2 ⟨subd6_11_82, List.forall_mem_cons.2 ⟨subd6_11_83, List.forall_mem_cons.2 ⟨subd6_11_84, List.forall_mem_cons.2 ⟨subd6_11_85, List.forall_mem_cons.2 ⟨subd6_11_86, List.forall_mem_cons.2 ⟨subd6_11_87, List.forall_mem_cons.2 ⟨subd6_11_88, List.forall_mem_cons.2 ⟨subd6_11_89, List.forall_mem_cons.2 ⟨subd6_11_90, List.forall_mem_cons.2 ⟨subd6_11_91, List.forall_mem_cons.2 ⟨subd6_11_92, List.forall_mem_cons.2 ⟨subd6_11_93, List.forall_mem_cons.2 ⟨subd6_11_94, List.forall_mem_cons.2 ⟨subd6_11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
