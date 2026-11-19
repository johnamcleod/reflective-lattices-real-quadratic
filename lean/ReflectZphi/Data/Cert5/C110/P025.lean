import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_32 : subd9_2 [-1, -4] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [-1, -3] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [-1, -2] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [-1, -1] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [-1, 0] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [-1, 1] = true := by decide +kernel
theorem subd9_2_38 : subd9_2 [-1, 2] = true := by decide +kernel
theorem subd9_2_39 : subd9_2 [-1, 3] = true := by decide +kernel
theorem subd9_2_40 : subd9_2 [-1, 4] = true := by decide +kernel
theorem subd9_2_41 : subd9_2 [-1, 5] = true := by decide +kernel
theorem subd9_2_42 : subd9_2 [0, -6] = true := by decide +kernel
theorem subd9_2_43 : subd9_2 [0, -5] = true := by decide +kernel
theorem subd9_2_44 : subd9_2 [0, -4] = true := by decide +kernel
theorem subd9_2_45 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_46 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_47 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_48 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_49 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_50 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_51 : subd9_2 [0, 3] = true := by decide +kernel
theorem subd9_2_52 : subd9_2 [0, 4] = true := by decide +kernel
theorem subd9_2_53 : subd9_2 [0, 5] = true := by decide +kernel
theorem subd9_2_54 : subd9_2 [1, -6] = true := by decide +kernel
theorem subd9_2_55 : subd9_2 [1, -5] = true := by decide +kernel
theorem subd9_2_56 : subd9_2 [1, -4] = true := by decide +kernel
theorem subd9_2_57 : subd9_2 [1, -3] = true := by decide +kernel
theorem subd9_2_58 : subd9_2 [1, -2] = true := by decide +kernel
theorem subd9_2_59 : subd9_2 [1, -1] = true := by decide +kernel
theorem subd9_2_60 : subd9_2 [1, 0] = true := by decide +kernel
theorem subd9_2_61 : subd9_2 [1, 1] = true := by decide +kernel
theorem subd9_2_62 : subd9_2 [1, 2] = true := by decide +kernel
theorem subd9_2_63 : subd9_2 [1, 3] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_cons.2 ⟨subd9_2_38, List.forall_mem_cons.2 ⟨subd9_2_39, List.forall_mem_cons.2 ⟨subd9_2_40, List.forall_mem_cons.2 ⟨subd9_2_41, List.forall_mem_cons.2 ⟨subd9_2_42, List.forall_mem_cons.2 ⟨subd9_2_43, List.forall_mem_cons.2 ⟨subd9_2_44, List.forall_mem_cons.2 ⟨subd9_2_45, List.forall_mem_cons.2 ⟨subd9_2_46, List.forall_mem_cons.2 ⟨subd9_2_47, List.forall_mem_cons.2 ⟨subd9_2_48, List.forall_mem_cons.2 ⟨subd9_2_49, List.forall_mem_cons.2 ⟨subd9_2_50, List.forall_mem_cons.2 ⟨subd9_2_51, List.forall_mem_cons.2 ⟨subd9_2_52, List.forall_mem_cons.2 ⟨subd9_2_53, List.forall_mem_cons.2 ⟨subd9_2_54, List.forall_mem_cons.2 ⟨subd9_2_55, List.forall_mem_cons.2 ⟨subd9_2_56, List.forall_mem_cons.2 ⟨subd9_2_57, List.forall_mem_cons.2 ⟨subd9_2_58, List.forall_mem_cons.2 ⟨subd9_2_59, List.forall_mem_cons.2 ⟨subd9_2_60, List.forall_mem_cons.2 ⟨subd9_2_61, List.forall_mem_cons.2 ⟨subd9_2_62, List.forall_mem_cons.2 ⟨subd9_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_64 : subd9_2 [1, 4] = true := by decide +kernel
theorem subd9_2_65 : subd9_2 [1, 5] = true := by decide +kernel
theorem subd9_2_66 : subd9_2 [2, -5] = true := by decide +kernel
theorem subd9_2_67 : subd9_2 [2, -4] = true := by decide +kernel
theorem subd9_2_68 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_69 : subd9_2 [2, -2] = true := by decide +kernel
theorem subd9_2_70 : subd9_2 [2, -1] = true := by decide +kernel
theorem subd9_2_71 : subd9_2 [2, 0] = true := by decide +kernel
theorem subd9_2_72 : subd9_2 [2, 1] = true := by decide +kernel
theorem subd9_2_73 : subd9_2 [2, 2] = true := by decide +kernel
theorem subd9_2_74 : subd9_2 [2, 3] = true := by decide +kernel
theorem subd9_2_75 : subd9_2 [2, 4] = true := by decide +kernel
theorem subd9_2_76 : subd9_2 [2, 5] = true := by decide +kernel
theorem subd9_2_77 : subd9_2 [3, -5] = true := by decide +kernel
theorem subd9_2_78 : subd9_2 [3, -4] = true := by decide +kernel
theorem subd9_2_79 : subd9_2 [3, -3] = true := by decide +kernel
theorem subd9_2_80 : subd9_2 [3, -2] = true := by decide +kernel
theorem subd9_2_81 : subd9_2 [3, -1] = true := by decide +kernel
theorem subd9_2_82 : subd9_2 [3, 0] = true := by decide +kernel
theorem subd9_2_83 : subd9_2 [3, 1] = true := by decide +kernel
theorem subd9_2_84 : subd9_2 [3, 2] = true := by decide +kernel
theorem subd9_2_85 : subd9_2 [3, 3] = true := by decide +kernel
theorem subd9_2_86 : subd9_2 [3, 4] = true := by decide +kernel
theorem subd9_2_87 : subd9_2 [4, -4] = true := by decide +kernel
theorem subd9_2_88 : subd9_2 [4, -3] = true := by decide +kernel
theorem subd9_2_89 : subd9_2 [4, -2] = true := by decide +kernel
theorem subd9_2_90 : subd9_2 [4, -1] = true := by decide +kernel
theorem subd9_2_91 : subd9_2 [4, 0] = true := by decide +kernel
theorem subd9_2_92 : subd9_2 [4, 1] = true := by decide +kernel
theorem subd9_2_93 : subd9_2 [4, 2] = true := by decide +kernel
theorem subd9_2_94 : subd9_2 [4, 3] = true := by decide +kernel
theorem subd9_2_95 : subd9_2 [5] = true := by decide +kernel
theorem sbd9_2_2 : ∀ q ∈ blkd9_2_2, subd9_2 q = true := by
  unfold blkd9_2_2
  exact List.forall_mem_cons.2 ⟨subd9_2_64, List.forall_mem_cons.2 ⟨subd9_2_65, List.forall_mem_cons.2 ⟨subd9_2_66, List.forall_mem_cons.2 ⟨subd9_2_67, List.forall_mem_cons.2 ⟨subd9_2_68, List.forall_mem_cons.2 ⟨subd9_2_69, List.forall_mem_cons.2 ⟨subd9_2_70, List.forall_mem_cons.2 ⟨subd9_2_71, List.forall_mem_cons.2 ⟨subd9_2_72, List.forall_mem_cons.2 ⟨subd9_2_73, List.forall_mem_cons.2 ⟨subd9_2_74, List.forall_mem_cons.2 ⟨subd9_2_75, List.forall_mem_cons.2 ⟨subd9_2_76, List.forall_mem_cons.2 ⟨subd9_2_77, List.forall_mem_cons.2 ⟨subd9_2_78, List.forall_mem_cons.2 ⟨subd9_2_79, List.forall_mem_cons.2 ⟨subd9_2_80, List.forall_mem_cons.2 ⟨subd9_2_81, List.forall_mem_cons.2 ⟨subd9_2_82, List.forall_mem_cons.2 ⟨subd9_2_83, List.forall_mem_cons.2 ⟨subd9_2_84, List.forall_mem_cons.2 ⟨subd9_2_85, List.forall_mem_cons.2 ⟨subd9_2_86, List.forall_mem_cons.2 ⟨subd9_2_87, List.forall_mem_cons.2 ⟨subd9_2_88, List.forall_mem_cons.2 ⟨subd9_2_89, List.forall_mem_cons.2 ⟨subd9_2_90, List.forall_mem_cons.2 ⟨subd9_2_91, List.forall_mem_cons.2 ⟨subd9_2_92, List.forall_mem_cons.2 ⟨subd9_2_93, List.forall_mem_cons.2 ⟨subd9_2_94, List.forall_mem_cons.2 ⟨subd9_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
