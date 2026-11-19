import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_32 : subd6_2 [-3, -7] = true := by decide +kernel
theorem subd6_2_33 : subd6_2 [-3, -6] = true := by decide +kernel
theorem subd6_2_34 : subd6_2 [-3, -5] = true := by decide +kernel
theorem subd6_2_35 : subd6_2 [-3, -4] = true := by decide +kernel
theorem subd6_2_36 : subd6_2 [-3, -3] = true := by decide +kernel
theorem subd6_2_37 : subd6_2 [-3, -2] = true := by decide +kernel
theorem subd6_2_38 : subd6_2 [-3, -1] = true := by decide +kernel
theorem subd6_2_39 : subd6_2 [-3, 0] = true := by decide +kernel
theorem subd6_2_40 : subd6_2 [-3, 1] = true := by decide +kernel
theorem subd6_2_41 : subd6_2 [-3, 2] = true := by decide +kernel
theorem subd6_2_42 : subd6_2 [-3, 3] = true := by decide +kernel
theorem subd6_2_43 : subd6_2 [-3, 4] = true := by decide +kernel
theorem subd6_2_44 : subd6_2 [-3, 5] = true := by decide +kernel
theorem subd6_2_45 : subd6_2 [-2, -8] = true := by decide +kernel
theorem subd6_2_46 : subd6_2 [-2, -7] = true := by decide +kernel
theorem subd6_2_47 : subd6_2 [-2, -6] = true := by decide +kernel
theorem subd6_2_48 : subd6_2 [-2, -5] = true := by decide +kernel
theorem subd6_2_49 : subd6_2 [-2, -4] = true := by decide +kernel
theorem subd6_2_50 : subd6_2 [-2, -3] = true := by decide +kernel
theorem subd6_2_51 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_52 : subd6_2 [-2, -1] = true := by decide +kernel
theorem subd6_2_53 : subd6_2 [-2, 0] = true := by decide +kernel
theorem subd6_2_54 : subd6_2 [-2, 1] = true := by decide +kernel
theorem subd6_2_55 : subd6_2 [-2, 2] = true := by decide +kernel
theorem subd6_2_56 : subd6_2 [-2, 3] = true := by decide +kernel
theorem subd6_2_57 : subd6_2 [-2, 4] = true := by decide +kernel
theorem subd6_2_58 : subd6_2 [-2, 5] = true := by decide +kernel
theorem subd6_2_59 : subd6_2 [-1, -8] = true := by decide +kernel
theorem subd6_2_60 : subd6_2 [-1, -7] = true := by decide +kernel
theorem subd6_2_61 : subd6_2 [-1, -6] = true := by decide +kernel
theorem subd6_2_62 : subd6_2 [-1, -5] = true := by decide +kernel
theorem subd6_2_63 : subd6_2 [-1, -4] = true := by decide +kernel
theorem sbd6_2_1 : ∀ q ∈ blkd6_2_1, subd6_2 q = true := by
  unfold blkd6_2_1
  exact List.forall_mem_cons.2 ⟨subd6_2_32, List.forall_mem_cons.2 ⟨subd6_2_33, List.forall_mem_cons.2 ⟨subd6_2_34, List.forall_mem_cons.2 ⟨subd6_2_35, List.forall_mem_cons.2 ⟨subd6_2_36, List.forall_mem_cons.2 ⟨subd6_2_37, List.forall_mem_cons.2 ⟨subd6_2_38, List.forall_mem_cons.2 ⟨subd6_2_39, List.forall_mem_cons.2 ⟨subd6_2_40, List.forall_mem_cons.2 ⟨subd6_2_41, List.forall_mem_cons.2 ⟨subd6_2_42, List.forall_mem_cons.2 ⟨subd6_2_43, List.forall_mem_cons.2 ⟨subd6_2_44, List.forall_mem_cons.2 ⟨subd6_2_45, List.forall_mem_cons.2 ⟨subd6_2_46, List.forall_mem_cons.2 ⟨subd6_2_47, List.forall_mem_cons.2 ⟨subd6_2_48, List.forall_mem_cons.2 ⟨subd6_2_49, List.forall_mem_cons.2 ⟨subd6_2_50, List.forall_mem_cons.2 ⟨subd6_2_51, List.forall_mem_cons.2 ⟨subd6_2_52, List.forall_mem_cons.2 ⟨subd6_2_53, List.forall_mem_cons.2 ⟨subd6_2_54, List.forall_mem_cons.2 ⟨subd6_2_55, List.forall_mem_cons.2 ⟨subd6_2_56, List.forall_mem_cons.2 ⟨subd6_2_57, List.forall_mem_cons.2 ⟨subd6_2_58, List.forall_mem_cons.2 ⟨subd6_2_59, List.forall_mem_cons.2 ⟨subd6_2_60, List.forall_mem_cons.2 ⟨subd6_2_61, List.forall_mem_cons.2 ⟨subd6_2_62, List.forall_mem_cons.2 ⟨subd6_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_64 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_65 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_66 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_67 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_68 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_69 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_70 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_71 : subd6_2 [-1, 4] = true := by decide +kernel
theorem subd6_2_72 : subd6_2 [-1, 5] = true := by decide +kernel
theorem subd6_2_73 : subd6_2 [-1, 6] = true := by decide +kernel
theorem subd6_2_74 : subd6_2 [0, -7] = true := by decide +kernel
theorem subd6_2_75 : subd6_2 [0, -6] = true := by decide +kernel
theorem subd6_2_76 : subd6_2 [0, -5] = true := by decide +kernel
theorem subd6_2_77 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_78 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_79 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_80 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_81 : subd6_2 [0, 0, -8] = true := by decide +kernel
theorem subd6_2_82 : subd6_2 [0, 0, -7] = true := by decide +kernel
theorem subd6_2_83 : subd6_2 [0, 0, -6] = true := by decide +kernel
theorem subd6_2_84 : subd6_2 [0, 0, -5] = true := by decide +kernel
theorem subd6_2_85 : subd6_2 [0, 0, -4] = true := by decide +kernel
theorem subd6_2_86 : subd6_2 [0, 0, -3] = true := by decide +kernel
theorem subd6_2_87 : subd6_2 [0, 0, -2] = true := by decide +kernel
theorem subd6_2_88 : subd6_2 [0, 0, -1] = true := by decide +kernel
theorem subd6_2_89 : subd6_2 [0, 0, 0] = true := by decide +kernel
theorem subd6_2_90 : subd6_2 [0, 0, 1] = true := by decide +kernel
theorem subd6_2_91 : subd6_2 [0, 0, 2] = true := by decide +kernel
theorem subd6_2_92 : subd6_2 [0, 0, 3] = true := by decide +kernel
theorem subd6_2_93 : subd6_2 [0, 0, 4] = true := by decide +kernel
theorem subd6_2_94 : subd6_2 [0, 0, 5] = true := by decide +kernel
theorem subd6_2_95 : subd6_2 [0, 0, 6] = true := by decide +kernel
theorem sbd6_2_2 : ∀ q ∈ blkd6_2_2, subd6_2 q = true := by
  unfold blkd6_2_2
  exact List.forall_mem_cons.2 ⟨subd6_2_64, List.forall_mem_cons.2 ⟨subd6_2_65, List.forall_mem_cons.2 ⟨subd6_2_66, List.forall_mem_cons.2 ⟨subd6_2_67, List.forall_mem_cons.2 ⟨subd6_2_68, List.forall_mem_cons.2 ⟨subd6_2_69, List.forall_mem_cons.2 ⟨subd6_2_70, List.forall_mem_cons.2 ⟨subd6_2_71, List.forall_mem_cons.2 ⟨subd6_2_72, List.forall_mem_cons.2 ⟨subd6_2_73, List.forall_mem_cons.2 ⟨subd6_2_74, List.forall_mem_cons.2 ⟨subd6_2_75, List.forall_mem_cons.2 ⟨subd6_2_76, List.forall_mem_cons.2 ⟨subd6_2_77, List.forall_mem_cons.2 ⟨subd6_2_78, List.forall_mem_cons.2 ⟨subd6_2_79, List.forall_mem_cons.2 ⟨subd6_2_80, List.forall_mem_cons.2 ⟨subd6_2_81, List.forall_mem_cons.2 ⟨subd6_2_82, List.forall_mem_cons.2 ⟨subd6_2_83, List.forall_mem_cons.2 ⟨subd6_2_84, List.forall_mem_cons.2 ⟨subd6_2_85, List.forall_mem_cons.2 ⟨subd6_2_86, List.forall_mem_cons.2 ⟨subd6_2_87, List.forall_mem_cons.2 ⟨subd6_2_88, List.forall_mem_cons.2 ⟨subd6_2_89, List.forall_mem_cons.2 ⟨subd6_2_90, List.forall_mem_cons.2 ⟨subd6_2_91, List.forall_mem_cons.2 ⟨subd6_2_92, List.forall_mem_cons.2 ⟨subd6_2_93, List.forall_mem_cons.2 ⟨subd6_2_94, List.forall_mem_cons.2 ⟨subd6_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
