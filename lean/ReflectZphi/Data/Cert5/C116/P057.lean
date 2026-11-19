import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_1_32 : subd14_1 [-2, 5] = true := by decide +kernel
theorem subd14_1_33 : subd14_1 [-1, -6] = true := by decide +kernel
theorem subd14_1_34 : subd14_1 [-1, -5] = true := by decide +kernel
theorem subd14_1_35 : subd14_1 [-1, -4] = true := by decide +kernel
theorem subd14_1_36 : subd14_1 [-1, -3] = true := by decide +kernel
theorem subd14_1_37 : subd14_1 [-1, -2] = true := by decide +kernel
theorem subd14_1_38 : subd14_1 [-1, -1] = true := by decide +kernel
theorem subd14_1_39 : subd14_1 [-1, 0] = true := by decide +kernel
theorem subd14_1_40 : subd14_1 [-1, 1] = true := by decide +kernel
theorem subd14_1_41 : subd14_1 [-1, 2] = true := by decide +kernel
theorem subd14_1_42 : subd14_1 [-1, 3] = true := by decide +kernel
theorem subd14_1_43 : subd14_1 [-1, 4] = true := by decide +kernel
theorem subd14_1_44 : subd14_1 [-1, 5] = true := by decide +kernel
theorem subd14_1_45 : subd14_1 [0, -6] = true := by decide +kernel
theorem subd14_1_46 : subd14_1 [0, -5] = true := by decide +kernel
theorem subd14_1_47 : subd14_1 [0, -4] = true := by decide +kernel
theorem subd14_1_48 : subd14_1 [0, -3] = true := by decide +kernel
theorem subd14_1_49 : subd14_1 [0, -2] = true := by decide +kernel
theorem subd14_1_50 : subd14_1 [0, -1] = true := by decide +kernel
theorem subd14_1_51 : subd14_1 [0, 0] = true := by decide +kernel
theorem subd14_1_52 : subd14_1 [0, 1] = true := by decide +kernel
theorem subd14_1_53 : subd14_1 [0, 2] = true := by decide +kernel
theorem subd14_1_54 : subd14_1 [0, 3] = true := by decide +kernel
theorem subd14_1_55 : subd14_1 [0, 4] = true := by decide +kernel
theorem subd14_1_56 : subd14_1 [0, 5] = true := by decide +kernel
theorem subd14_1_57 : subd14_1 [1, -6] = true := by decide +kernel
theorem subd14_1_58 : subd14_1 [1, -5] = true := by decide +kernel
theorem subd14_1_59 : subd14_1 [1, -4] = true := by decide +kernel
theorem subd14_1_60 : subd14_1 [1, -3] = true := by decide +kernel
theorem subd14_1_61 : subd14_1 [1, -2] = true := by decide +kernel
theorem subd14_1_62 : subd14_1 [1, -1] = true := by decide +kernel
theorem subd14_1_63 : subd14_1 [1, 0] = true := by decide +kernel
theorem sbd14_1_1 : ∀ q ∈ blkd14_1_1, subd14_1 q = true := by
  unfold blkd14_1_1
  exact List.forall_mem_cons.2 ⟨subd14_1_32, List.forall_mem_cons.2 ⟨subd14_1_33, List.forall_mem_cons.2 ⟨subd14_1_34, List.forall_mem_cons.2 ⟨subd14_1_35, List.forall_mem_cons.2 ⟨subd14_1_36, List.forall_mem_cons.2 ⟨subd14_1_37, List.forall_mem_cons.2 ⟨subd14_1_38, List.forall_mem_cons.2 ⟨subd14_1_39, List.forall_mem_cons.2 ⟨subd14_1_40, List.forall_mem_cons.2 ⟨subd14_1_41, List.forall_mem_cons.2 ⟨subd14_1_42, List.forall_mem_cons.2 ⟨subd14_1_43, List.forall_mem_cons.2 ⟨subd14_1_44, List.forall_mem_cons.2 ⟨subd14_1_45, List.forall_mem_cons.2 ⟨subd14_1_46, List.forall_mem_cons.2 ⟨subd14_1_47, List.forall_mem_cons.2 ⟨subd14_1_48, List.forall_mem_cons.2 ⟨subd14_1_49, List.forall_mem_cons.2 ⟨subd14_1_50, List.forall_mem_cons.2 ⟨subd14_1_51, List.forall_mem_cons.2 ⟨subd14_1_52, List.forall_mem_cons.2 ⟨subd14_1_53, List.forall_mem_cons.2 ⟨subd14_1_54, List.forall_mem_cons.2 ⟨subd14_1_55, List.forall_mem_cons.2 ⟨subd14_1_56, List.forall_mem_cons.2 ⟨subd14_1_57, List.forall_mem_cons.2 ⟨subd14_1_58, List.forall_mem_cons.2 ⟨subd14_1_59, List.forall_mem_cons.2 ⟨subd14_1_60, List.forall_mem_cons.2 ⟨subd14_1_61, List.forall_mem_cons.2 ⟨subd14_1_62, List.forall_mem_cons.2 ⟨subd14_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_64 : subd14_1 [1, 1] = true := by decide +kernel
theorem subd14_1_65 : subd14_1 [1, 2] = true := by decide +kernel
theorem subd14_1_66 : subd14_1 [1, 3] = true := by decide +kernel
theorem subd14_1_67 : subd14_1 [1, 4] = true := by decide +kernel
theorem subd14_1_68 : subd14_1 [1, 5] = true := by decide +kernel
theorem subd14_1_69 : subd14_1 [2, -6] = true := by decide +kernel
theorem subd14_1_70 : subd14_1 [2, -5] = true := by decide +kernel
theorem subd14_1_71 : subd14_1 [2, -4] = true := by decide +kernel
theorem subd14_1_72 : subd14_1 [2, -3] = true := by decide +kernel
theorem subd14_1_73 : subd14_1 [2, -2] = true := by decide +kernel
theorem subd14_1_74 : subd14_1 [2, -1] = true := by decide +kernel
theorem subd14_1_75 : subd14_1 [2, 0] = true := by decide +kernel
theorem subd14_1_76 : subd14_1 [2, 1] = true := by decide +kernel
theorem subd14_1_77 : subd14_1 [2, 2] = true := by decide +kernel
theorem subd14_1_78 : subd14_1 [2, 3] = true := by decide +kernel
theorem subd14_1_79 : subd14_1 [2, 4] = true := by decide +kernel
theorem subd14_1_80 : subd14_1 [2, 5] = true := by decide +kernel
theorem subd14_1_81 : subd14_1 [3, -6] = true := by decide +kernel
theorem subd14_1_82 : subd14_1 [3, -5] = true := by decide +kernel
theorem subd14_1_83 : subd14_1 [3, -4] = true := by decide +kernel
theorem subd14_1_84 : subd14_1 [3, -3] = true := by decide +kernel
theorem subd14_1_85 : subd14_1 [3, -2] = true := by decide +kernel
theorem subd14_1_86 : subd14_1 [3, -1] = true := by decide +kernel
theorem subd14_1_87 : subd14_1 [3, 0] = true := by decide +kernel
theorem subd14_1_88 : subd14_1 [3, 1] = true := by decide +kernel
theorem subd14_1_89 : subd14_1 [3, 2] = true := by decide +kernel
theorem subd14_1_90 : subd14_1 [3, 3] = true := by decide +kernel
theorem subd14_1_91 : subd14_1 [3, 4] = true := by decide +kernel
theorem subd14_1_92 : subd14_1 [4, -5] = true := by decide +kernel
theorem subd14_1_93 : subd14_1 [4, -4] = true := by decide +kernel
theorem subd14_1_94 : subd14_1 [4, -3] = true := by decide +kernel
theorem subd14_1_95 : subd14_1 [4, -2] = true := by decide +kernel
theorem sbd14_1_2 : ∀ q ∈ blkd14_1_2, subd14_1 q = true := by
  unfold blkd14_1_2
  exact List.forall_mem_cons.2 ⟨subd14_1_64, List.forall_mem_cons.2 ⟨subd14_1_65, List.forall_mem_cons.2 ⟨subd14_1_66, List.forall_mem_cons.2 ⟨subd14_1_67, List.forall_mem_cons.2 ⟨subd14_1_68, List.forall_mem_cons.2 ⟨subd14_1_69, List.forall_mem_cons.2 ⟨subd14_1_70, List.forall_mem_cons.2 ⟨subd14_1_71, List.forall_mem_cons.2 ⟨subd14_1_72, List.forall_mem_cons.2 ⟨subd14_1_73, List.forall_mem_cons.2 ⟨subd14_1_74, List.forall_mem_cons.2 ⟨subd14_1_75, List.forall_mem_cons.2 ⟨subd14_1_76, List.forall_mem_cons.2 ⟨subd14_1_77, List.forall_mem_cons.2 ⟨subd14_1_78, List.forall_mem_cons.2 ⟨subd14_1_79, List.forall_mem_cons.2 ⟨subd14_1_80, List.forall_mem_cons.2 ⟨subd14_1_81, List.forall_mem_cons.2 ⟨subd14_1_82, List.forall_mem_cons.2 ⟨subd14_1_83, List.forall_mem_cons.2 ⟨subd14_1_84, List.forall_mem_cons.2 ⟨subd14_1_85, List.forall_mem_cons.2 ⟨subd14_1_86, List.forall_mem_cons.2 ⟨subd14_1_87, List.forall_mem_cons.2 ⟨subd14_1_88, List.forall_mem_cons.2 ⟨subd14_1_89, List.forall_mem_cons.2 ⟨subd14_1_90, List.forall_mem_cons.2 ⟨subd14_1_91, List.forall_mem_cons.2 ⟨subd14_1_92, List.forall_mem_cons.2 ⟨subd14_1_93, List.forall_mem_cons.2 ⟨subd14_1_94, List.forall_mem_cons.2 ⟨subd14_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_96 : subd14_1 [4, -1] = true := by decide +kernel
theorem subd14_1_97 : subd14_1 [4, 0] = true := by decide +kernel
theorem subd14_1_98 : subd14_1 [4, 1] = true := by decide +kernel
theorem subd14_1_99 : subd14_1 [4, 2] = true := by decide +kernel
theorem subd14_1_100 : subd14_1 [4, 3] = true := by decide +kernel
theorem subd14_1_101 : subd14_1 [5] = true := by decide +kernel
theorem sbd14_1_3 : ∀ q ∈ blkd14_1_3, subd14_1 q = true := by
  unfold blkd14_1_3
  exact List.forall_mem_cons.2 ⟨subd14_1_96, List.forall_mem_cons.2 ⟨subd14_1_97, List.forall_mem_cons.2 ⟨subd14_1_98, List.forall_mem_cons.2 ⟨subd14_1_99, List.forall_mem_cons.2 ⟨subd14_1_100, List.forall_mem_cons.2 ⟨subd14_1_101, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_nil _⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-2] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-1, -4] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-1, -3] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-1, -1] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-1, 0] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-1, 2] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [0, -3] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [0, -1] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [0, 0] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [0, 1] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [0, 2] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [1, -3] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [1, 0] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [1, 1] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [1, 2] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [1, 3] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [2] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_nil _⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C116
