import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_32 : subd8_1 [-4, 1] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [-4, 2] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [-4, 3] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [-4, 4] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [-3, -9] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [-3, -8] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [-3, -7] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [-3, -6] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [-3, -5] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [-3, -4] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [-3, -3] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [-3, -2] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [-3, -1] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [-3, 0] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [-3, 1] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [-3, 2] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [-3, 3] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [-3, 4] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [-3, 5] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [-2, -9] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [-2, -8] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [-2, -7] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [-2, -6] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [-2, -5] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [-2, 3] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [-2, 4] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [-2, 5] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [-2, 6] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [-1, -9] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [-1, -8] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [-1, -7] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [-1, -6] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [-1, -5] = true := by decide +kernel
theorem subd8_1_72 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_73 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_74 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_75 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_76 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_77 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_78 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_79 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_80 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_81 : subd8_1 [-1, 5] = true := by decide +kernel
theorem subd8_1_82 : subd8_1 [-1, 6] = true := by decide +kernel
theorem subd8_1_83 : subd8_1 [-1, 7] = true := by decide +kernel
theorem subd8_1_84 : subd8_1 [0, -8] = true := by decide +kernel
theorem subd8_1_85 : subd8_1 [0, -7] = true := by decide +kernel
theorem subd8_1_86 : subd8_1 [0, -6] = true := by decide +kernel
theorem subd8_1_87 : subd8_1 [0, -5] = true := by decide +kernel
theorem subd8_1_88 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_89 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_90 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_91 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_92 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_93 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_94 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_95 : subd8_1 [0, 3] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_cons.2 ⟨subd8_1_72, List.forall_mem_cons.2 ⟨subd8_1_73, List.forall_mem_cons.2 ⟨subd8_1_74, List.forall_mem_cons.2 ⟨subd8_1_75, List.forall_mem_cons.2 ⟨subd8_1_76, List.forall_mem_cons.2 ⟨subd8_1_77, List.forall_mem_cons.2 ⟨subd8_1_78, List.forall_mem_cons.2 ⟨subd8_1_79, List.forall_mem_cons.2 ⟨subd8_1_80, List.forall_mem_cons.2 ⟨subd8_1_81, List.forall_mem_cons.2 ⟨subd8_1_82, List.forall_mem_cons.2 ⟨subd8_1_83, List.forall_mem_cons.2 ⟨subd8_1_84, List.forall_mem_cons.2 ⟨subd8_1_85, List.forall_mem_cons.2 ⟨subd8_1_86, List.forall_mem_cons.2 ⟨subd8_1_87, List.forall_mem_cons.2 ⟨subd8_1_88, List.forall_mem_cons.2 ⟨subd8_1_89, List.forall_mem_cons.2 ⟨subd8_1_90, List.forall_mem_cons.2 ⟨subd8_1_91, List.forall_mem_cons.2 ⟨subd8_1_92, List.forall_mem_cons.2 ⟨subd8_1_93, List.forall_mem_cons.2 ⟨subd8_1_94, List.forall_mem_cons.2 ⟨subd8_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
