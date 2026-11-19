import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_7_32 : subd6_7 [-3, 2] = true := by decide +kernel
theorem subd6_7_33 : subd6_7 [-3, 3] = true := by decide +kernel
theorem subd6_7_34 : subd6_7 [-3, 4] = true := by decide +kernel
theorem subd6_7_35 : subd6_7 [-2, -8] = true := by decide +kernel
theorem subd6_7_36 : subd6_7 [-2, -7] = true := by decide +kernel
theorem subd6_7_37 : subd6_7 [-2, -6] = true := by decide +kernel
theorem subd6_7_38 : subd6_7 [-2, -5] = true := by decide +kernel
theorem subd6_7_39 : subd6_7 [-2, -4] = true := by decide +kernel
theorem subd6_7_40 : subd6_7 [-2, -3] = true := by decide +kernel
theorem subd6_7_41 : subd6_7 [-2, -2] = true := by decide +kernel
theorem subd6_7_42 : subd6_7 [-2, -1] = true := by decide +kernel
theorem subd6_7_43 : subd6_7 [-2, 0] = true := by decide +kernel
theorem subd6_7_44 : subd6_7 [-2, 1] = true := by decide +kernel
theorem subd6_7_45 : subd6_7 [-2, 2] = true := by decide +kernel
theorem subd6_7_46 : subd6_7 [-2, 3] = true := by decide +kernel
theorem subd6_7_47 : subd6_7 [-2, 4] = true := by decide +kernel
theorem subd6_7_48 : subd6_7 [-2, 5] = true := by decide +kernel
theorem subd6_7_49 : subd6_7 [-1, -8] = true := by decide +kernel
theorem subd6_7_50 : subd6_7 [-1, -7] = true := by decide +kernel
theorem subd6_7_51 : subd6_7 [-1, -6] = true := by decide +kernel
theorem subd6_7_52 : subd6_7 [-1, -5] = true := by decide +kernel
theorem subd6_7_53 : subd6_7 [-1, -4] = true := by decide +kernel
theorem subd6_7_54 : subd6_7 [-1, -3] = true := by decide +kernel
theorem subd6_7_55 : subd6_7 [-1, -2] = true := by decide +kernel
theorem subd6_7_56 : subd6_7 [-1, -1] = true := by decide +kernel
theorem subd6_7_57 : subd6_7 [-1, 0] = true := by decide +kernel
theorem subd6_7_58 : subd6_7 [-1, 1] = true := by decide +kernel
theorem subd6_7_59 : subd6_7 [-1, 2] = true := by decide +kernel
theorem subd6_7_60 : subd6_7 [-1, 3] = true := by decide +kernel
theorem subd6_7_61 : subd6_7 [-1, 4] = true := by decide +kernel
theorem subd6_7_62 : subd6_7 [-1, 5] = true := by decide +kernel
theorem subd6_7_63 : subd6_7 [-1, 6] = true := by decide +kernel
theorem sbd6_7_1 : ∀ q ∈ blkd6_7_1, subd6_7 q = true := by
  unfold blkd6_7_1
  exact List.forall_mem_cons.2 ⟨subd6_7_32, List.forall_mem_cons.2 ⟨subd6_7_33, List.forall_mem_cons.2 ⟨subd6_7_34, List.forall_mem_cons.2 ⟨subd6_7_35, List.forall_mem_cons.2 ⟨subd6_7_36, List.forall_mem_cons.2 ⟨subd6_7_37, List.forall_mem_cons.2 ⟨subd6_7_38, List.forall_mem_cons.2 ⟨subd6_7_39, List.forall_mem_cons.2 ⟨subd6_7_40, List.forall_mem_cons.2 ⟨subd6_7_41, List.forall_mem_cons.2 ⟨subd6_7_42, List.forall_mem_cons.2 ⟨subd6_7_43, List.forall_mem_cons.2 ⟨subd6_7_44, List.forall_mem_cons.2 ⟨subd6_7_45, List.forall_mem_cons.2 ⟨subd6_7_46, List.forall_mem_cons.2 ⟨subd6_7_47, List.forall_mem_cons.2 ⟨subd6_7_48, List.forall_mem_cons.2 ⟨subd6_7_49, List.forall_mem_cons.2 ⟨subd6_7_50, List.forall_mem_cons.2 ⟨subd6_7_51, List.forall_mem_cons.2 ⟨subd6_7_52, List.forall_mem_cons.2 ⟨subd6_7_53, List.forall_mem_cons.2 ⟨subd6_7_54, List.forall_mem_cons.2 ⟨subd6_7_55, List.forall_mem_cons.2 ⟨subd6_7_56, List.forall_mem_cons.2 ⟨subd6_7_57, List.forall_mem_cons.2 ⟨subd6_7_58, List.forall_mem_cons.2 ⟨subd6_7_59, List.forall_mem_cons.2 ⟨subd6_7_60, List.forall_mem_cons.2 ⟨subd6_7_61, List.forall_mem_cons.2 ⟨subd6_7_62, List.forall_mem_cons.2 ⟨subd6_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_64 : subd6_7 [0, -7] = true := by decide +kernel
theorem subd6_7_65 : subd6_7 [0, -6] = true := by decide +kernel
theorem subd6_7_66 : subd6_7 [0, -5] = true := by decide +kernel
theorem subd6_7_67 : subd6_7 [0, -4] = true := by decide +kernel
theorem subd6_7_68 : subd6_7 [0, -3] = true := by decide +kernel
theorem subd6_7_69 : subd6_7 [0, -2] = true := by decide +kernel
theorem subd6_7_70 : subd6_7 [0, -1] = true := by decide +kernel
theorem subd6_7_71 : subd6_7 [0, 0] = true := by decide +kernel
theorem subd6_7_72 : subd6_7 [0, 1] = true := by decide +kernel
theorem subd6_7_73 : subd6_7 [0, 2] = true := by decide +kernel
theorem subd6_7_74 : subd6_7 [0, 3] = true := by decide +kernel
theorem subd6_7_75 : subd6_7 [0, 4] = true := by decide +kernel
theorem subd6_7_76 : subd6_7 [0, 5] = true := by decide +kernel
theorem subd6_7_77 : subd6_7 [0, 6] = true := by decide +kernel
theorem subd6_7_78 : subd6_7 [1, -7] = true := by decide +kernel
theorem subd6_7_79 : subd6_7 [1, -6] = true := by decide +kernel
theorem subd6_7_80 : subd6_7 [1, -5] = true := by decide +kernel
theorem subd6_7_81 : subd6_7 [1, -4] = true := by decide +kernel
theorem subd6_7_82 : subd6_7 [1, -3] = true := by decide +kernel
theorem subd6_7_83 : subd6_7 [1, -2] = true := by decide +kernel
theorem subd6_7_84 : subd6_7 [1, -1] = true := by decide +kernel
theorem subd6_7_85 : subd6_7 [1, 0] = true := by decide +kernel
theorem subd6_7_86 : subd6_7 [1, 1] = true := by decide +kernel
theorem subd6_7_87 : subd6_7 [1, 2] = true := by decide +kernel
theorem subd6_7_88 : subd6_7 [1, 3] = true := by decide +kernel
theorem subd6_7_89 : subd6_7 [1, 4] = true := by decide +kernel
theorem subd6_7_90 : subd6_7 [1, 5] = true := by decide +kernel
theorem subd6_7_91 : subd6_7 [1, 6] = true := by decide +kernel
theorem subd6_7_92 : subd6_7 [1, 7] = true := by decide +kernel
theorem subd6_7_93 : subd6_7 [2, -6] = true := by decide +kernel
theorem subd6_7_94 : subd6_7 [2, -5] = true := by decide +kernel
theorem subd6_7_95 : subd6_7 [2, -4] = true := by decide +kernel
theorem sbd6_7_2 : ∀ q ∈ blkd6_7_2, subd6_7 q = true := by
  unfold blkd6_7_2
  exact List.forall_mem_cons.2 ⟨subd6_7_64, List.forall_mem_cons.2 ⟨subd6_7_65, List.forall_mem_cons.2 ⟨subd6_7_66, List.forall_mem_cons.2 ⟨subd6_7_67, List.forall_mem_cons.2 ⟨subd6_7_68, List.forall_mem_cons.2 ⟨subd6_7_69, List.forall_mem_cons.2 ⟨subd6_7_70, List.forall_mem_cons.2 ⟨subd6_7_71, List.forall_mem_cons.2 ⟨subd6_7_72, List.forall_mem_cons.2 ⟨subd6_7_73, List.forall_mem_cons.2 ⟨subd6_7_74, List.forall_mem_cons.2 ⟨subd6_7_75, List.forall_mem_cons.2 ⟨subd6_7_76, List.forall_mem_cons.2 ⟨subd6_7_77, List.forall_mem_cons.2 ⟨subd6_7_78, List.forall_mem_cons.2 ⟨subd6_7_79, List.forall_mem_cons.2 ⟨subd6_7_80, List.forall_mem_cons.2 ⟨subd6_7_81, List.forall_mem_cons.2 ⟨subd6_7_82, List.forall_mem_cons.2 ⟨subd6_7_83, List.forall_mem_cons.2 ⟨subd6_7_84, List.forall_mem_cons.2 ⟨subd6_7_85, List.forall_mem_cons.2 ⟨subd6_7_86, List.forall_mem_cons.2 ⟨subd6_7_87, List.forall_mem_cons.2 ⟨subd6_7_88, List.forall_mem_cons.2 ⟨subd6_7_89, List.forall_mem_cons.2 ⟨subd6_7_90, List.forall_mem_cons.2 ⟨subd6_7_91, List.forall_mem_cons.2 ⟨subd6_7_92, List.forall_mem_cons.2 ⟨subd6_7_93, List.forall_mem_cons.2 ⟨subd6_7_94, List.forall_mem_cons.2 ⟨subd6_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
