import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_9_32 : subd8_9 [-1, 0, -7] = true := by decide +kernel
theorem subd8_9_33 : subd8_9 [-1, 0, -6] = true := by decide +kernel
theorem subd8_9_34 : subd8_9 [-1, 0, -5] = true := by decide +kernel
theorem subd8_9_35 : subd8_9 [-1, 0, -4] = true := by decide +kernel
theorem subd8_9_36 : subd8_9 [-1, 0, -3] = true := by decide +kernel
theorem subd8_9_37 : subd8_9 [-1, 0, -2] = true := by decide +kernel
theorem subd8_9_38 : subd8_9 [-1, 0, -1] = true := by decide +kernel
theorem subd8_9_39 : subd8_9 [-1, 0, 0] = true := by decide +kernel
theorem subd8_9_40 : subd8_9 [-1, 0, 1] = true := by decide +kernel
theorem subd8_9_41 : subd8_9 [-1, 0, 2] = true := by decide +kernel
theorem subd8_9_42 : subd8_9 [-1, 0, 3] = true := by decide +kernel
theorem subd8_9_43 : subd8_9 [-1, 0, 4] = true := by decide +kernel
theorem subd8_9_44 : subd8_9 [-1, 0, 5] = true := by decide +kernel
theorem subd8_9_45 : subd8_9 [-1, 1] = true := by decide +kernel
theorem subd8_9_46 : subd8_9 [-1, 2] = true := by decide +kernel
theorem subd8_9_47 : subd8_9 [-1, 3] = true := by decide +kernel
theorem subd8_9_48 : subd8_9 [-1, 4] = true := by decide +kernel
theorem subd8_9_49 : subd8_9 [0, -6] = true := by decide +kernel
theorem subd8_9_50 : subd8_9 [0, -5] = true := by decide +kernel
theorem subd8_9_51 : subd8_9 [0, -4] = true := by decide +kernel
theorem subd8_9_52 : subd8_9 [0, -3] = true := by decide +kernel
theorem subd8_9_53 : subd8_9 [0, -2] = true := by decide +kernel
theorem subd8_9_54 : subd8_9 [0, -1] = true := by decide +kernel
theorem subd8_9_55 : subd8_9 [0, 0, -7] = true := by decide +kernel
theorem subd8_9_56 : subd8_9 [0, 0, -6] = true := by decide +kernel
theorem subd8_9_57 : subd8_9 [0, 0, -5] = true := by decide +kernel
theorem subd8_9_58 : subd8_9 [0, 0, -4] = true := by decide +kernel
theorem subd8_9_59 : subd8_9 [0, 0, -3] = true := by decide +kernel
theorem subd8_9_60 : subd8_9 [0, 0, -2] = true := by decide +kernel
theorem subd8_9_61 : subd8_9 [0, 0, -1] = true := by decide +kernel
theorem subd8_9_62 : subd8_9 [0, 0, 0] = true := by decide +kernel
theorem subd8_9_63 : subd8_9 [0, 0, 1] = true := by decide +kernel
theorem sbd8_9_1 : ∀ q ∈ blkd8_9_1, subd8_9 q = true := by
  unfold blkd8_9_1
  exact List.forall_mem_cons.2 ⟨subd8_9_32, List.forall_mem_cons.2 ⟨subd8_9_33, List.forall_mem_cons.2 ⟨subd8_9_34, List.forall_mem_cons.2 ⟨subd8_9_35, List.forall_mem_cons.2 ⟨subd8_9_36, List.forall_mem_cons.2 ⟨subd8_9_37, List.forall_mem_cons.2 ⟨subd8_9_38, List.forall_mem_cons.2 ⟨subd8_9_39, List.forall_mem_cons.2 ⟨subd8_9_40, List.forall_mem_cons.2 ⟨subd8_9_41, List.forall_mem_cons.2 ⟨subd8_9_42, List.forall_mem_cons.2 ⟨subd8_9_43, List.forall_mem_cons.2 ⟨subd8_9_44, List.forall_mem_cons.2 ⟨subd8_9_45, List.forall_mem_cons.2 ⟨subd8_9_46, List.forall_mem_cons.2 ⟨subd8_9_47, List.forall_mem_cons.2 ⟨subd8_9_48, List.forall_mem_cons.2 ⟨subd8_9_49, List.forall_mem_cons.2 ⟨subd8_9_50, List.forall_mem_cons.2 ⟨subd8_9_51, List.forall_mem_cons.2 ⟨subd8_9_52, List.forall_mem_cons.2 ⟨subd8_9_53, List.forall_mem_cons.2 ⟨subd8_9_54, List.forall_mem_cons.2 ⟨subd8_9_55, List.forall_mem_cons.2 ⟨subd8_9_56, List.forall_mem_cons.2 ⟨subd8_9_57, List.forall_mem_cons.2 ⟨subd8_9_58, List.forall_mem_cons.2 ⟨subd8_9_59, List.forall_mem_cons.2 ⟨subd8_9_60, List.forall_mem_cons.2 ⟨subd8_9_61, List.forall_mem_cons.2 ⟨subd8_9_62, List.forall_mem_cons.2 ⟨subd8_9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_9_64 : subd8_9 [0, 0, 2] = true := by decide +kernel
theorem subd8_9_65 : subd8_9 [0, 0, 3] = true := by decide +kernel
theorem subd8_9_66 : subd8_9 [0, 0, 4] = true := by decide +kernel
theorem subd8_9_67 : subd8_9 [0, 0, 5] = true := by decide +kernel
theorem subd8_9_68 : subd8_9 [0, 0, 6] = true := by decide +kernel
theorem subd8_9_69 : subd8_9 [0, 1] = true := by decide +kernel
theorem subd8_9_70 : subd8_9 [0, 2] = true := by decide +kernel
theorem subd8_9_71 : subd8_9 [0, 3] = true := by decide +kernel
theorem subd8_9_72 : subd8_9 [0, 4] = true := by decide +kernel
theorem subd8_9_73 : subd8_9 [0, 5] = true := by decide +kernel
theorem subd8_9_74 : subd8_9 [1, -5] = true := by decide +kernel
theorem subd8_9_75 : subd8_9 [1, -4] = true := by decide +kernel
theorem subd8_9_76 : subd8_9 [1, -3] = true := by decide +kernel
theorem subd8_9_77 : subd8_9 [1, -2] = true := by decide +kernel
theorem subd8_9_78 : subd8_9 [1, -1] = true := by decide +kernel
theorem subd8_9_79 : subd8_9 [1, 0, -6] = true := by decide +kernel
theorem subd8_9_80 : subd8_9 [1, 0, -5] = true := by decide +kernel
theorem subd8_9_81 : subd8_9 [1, 0, -4] = true := by decide +kernel
theorem subd8_9_82 : subd8_9 [1, 0, -3] = true := by decide +kernel
theorem subd8_9_83 : subd8_9 [1, 0, -2] = true := by decide +kernel
theorem subd8_9_84 : subd8_9 [1, 0, -1] = true := by decide +kernel
theorem subd8_9_85 : subd8_9 [1, 0, 0] = true := by decide +kernel
theorem subd8_9_86 : subd8_9 [1, 0, 1] = true := by decide +kernel
theorem subd8_9_87 : subd8_9 [1, 0, 2] = true := by decide +kernel
theorem subd8_9_88 : subd8_9 [1, 0, 3] = true := by decide +kernel
theorem subd8_9_89 : subd8_9 [1, 0, 4] = true := by decide +kernel
theorem subd8_9_90 : subd8_9 [1, 0, 5] = true := by decide +kernel
theorem subd8_9_91 : subd8_9 [1, 0, 6] = true := by decide +kernel
theorem subd8_9_92 : subd8_9 [1, 1] = true := by decide +kernel
theorem subd8_9_93 : subd8_9 [1, 2] = true := by decide +kernel
theorem subd8_9_94 : subd8_9 [1, 3] = true := by decide +kernel
theorem subd8_9_95 : subd8_9 [1, 4] = true := by decide +kernel
theorem sbd8_9_2 : ∀ q ∈ blkd8_9_2, subd8_9 q = true := by
  unfold blkd8_9_2
  exact List.forall_mem_cons.2 ⟨subd8_9_64, List.forall_mem_cons.2 ⟨subd8_9_65, List.forall_mem_cons.2 ⟨subd8_9_66, List.forall_mem_cons.2 ⟨subd8_9_67, List.forall_mem_cons.2 ⟨subd8_9_68, List.forall_mem_cons.2 ⟨subd8_9_69, List.forall_mem_cons.2 ⟨subd8_9_70, List.forall_mem_cons.2 ⟨subd8_9_71, List.forall_mem_cons.2 ⟨subd8_9_72, List.forall_mem_cons.2 ⟨subd8_9_73, List.forall_mem_cons.2 ⟨subd8_9_74, List.forall_mem_cons.2 ⟨subd8_9_75, List.forall_mem_cons.2 ⟨subd8_9_76, List.forall_mem_cons.2 ⟨subd8_9_77, List.forall_mem_cons.2 ⟨subd8_9_78, List.forall_mem_cons.2 ⟨subd8_9_79, List.forall_mem_cons.2 ⟨subd8_9_80, List.forall_mem_cons.2 ⟨subd8_9_81, List.forall_mem_cons.2 ⟨subd8_9_82, List.forall_mem_cons.2 ⟨subd8_9_83, List.forall_mem_cons.2 ⟨subd8_9_84, List.forall_mem_cons.2 ⟨subd8_9_85, List.forall_mem_cons.2 ⟨subd8_9_86, List.forall_mem_cons.2 ⟨subd8_9_87, List.forall_mem_cons.2 ⟨subd8_9_88, List.forall_mem_cons.2 ⟨subd8_9_89, List.forall_mem_cons.2 ⟨subd8_9_90, List.forall_mem_cons.2 ⟨subd8_9_91, List.forall_mem_cons.2 ⟨subd8_9_92, List.forall_mem_cons.2 ⟨subd8_9_93, List.forall_mem_cons.2 ⟨subd8_9_94, List.forall_mem_cons.2 ⟨subd8_9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_9_96 : subd8_9 [1, 5] = true := by decide +kernel
theorem subd8_9_97 : subd8_9 [2, -4] = true := by decide +kernel
theorem subd8_9_98 : subd8_9 [2, -3] = true := by decide +kernel
theorem subd8_9_99 : subd8_9 [2, -2] = true := by decide +kernel
theorem subd8_9_100 : subd8_9 [2, -1] = true := by decide +kernel
theorem subd8_9_101 : subd8_9 [2, 0] = true := by decide +kernel
theorem subd8_9_102 : subd8_9 [2, 1] = true := by decide +kernel
theorem subd8_9_103 : subd8_9 [2, 2] = true := by decide +kernel
theorem subd8_9_104 : subd8_9 [2, 3] = true := by decide +kernel
theorem subd8_9_105 : subd8_9 [2, 4] = true := by decide +kernel
theorem subd8_9_106 : subd8_9 [2, 5] = true := by decide +kernel
theorem subd8_9_107 : subd8_9 [3, -3] = true := by decide +kernel
theorem subd8_9_108 : subd8_9 [3, -2] = true := by decide +kernel
theorem subd8_9_109 : subd8_9 [3, -1] = true := by decide +kernel
theorem subd8_9_110 : subd8_9 [3, 0] = true := by decide +kernel
theorem subd8_9_111 : subd8_9 [3, 1] = true := by decide +kernel
theorem subd8_9_112 : subd8_9 [3, 2] = true := by decide +kernel
theorem subd8_9_113 : subd8_9 [3, 3] = true := by decide +kernel
theorem subd8_9_114 : subd8_9 [3, 4] = true := by decide +kernel
theorem subd8_9_115 : subd8_9 [3, 5] = true := by decide +kernel
theorem subd8_9_116 : subd8_9 [4, -2] = true := by decide +kernel
theorem subd8_9_117 : subd8_9 [4, -1] = true := by decide +kernel
theorem subd8_9_118 : subd8_9 [4, 0] = true := by decide +kernel
theorem subd8_9_119 : subd8_9 [4, 1] = true := by decide +kernel
theorem subd8_9_120 : subd8_9 [4, 2] = true := by decide +kernel
theorem subd8_9_121 : subd8_9 [4, 3] = true := by decide +kernel
theorem subd8_9_122 : subd8_9 [4, 4] = true := by decide +kernel
theorem sbd8_9_3 : ∀ q ∈ blkd8_9_3, subd8_9 q = true := by
  unfold blkd8_9_3
  exact List.forall_mem_cons.2 ⟨subd8_9_96, List.forall_mem_cons.2 ⟨subd8_9_97, List.forall_mem_cons.2 ⟨subd8_9_98, List.forall_mem_cons.2 ⟨subd8_9_99, List.forall_mem_cons.2 ⟨subd8_9_100, List.forall_mem_cons.2 ⟨subd8_9_101, List.forall_mem_cons.2 ⟨subd8_9_102, List.forall_mem_cons.2 ⟨subd8_9_103, List.forall_mem_cons.2 ⟨subd8_9_104, List.forall_mem_cons.2 ⟨subd8_9_105, List.forall_mem_cons.2 ⟨subd8_9_106, List.forall_mem_cons.2 ⟨subd8_9_107, List.forall_mem_cons.2 ⟨subd8_9_108, List.forall_mem_cons.2 ⟨subd8_9_109, List.forall_mem_cons.2 ⟨subd8_9_110, List.forall_mem_cons.2 ⟨subd8_9_111, List.forall_mem_cons.2 ⟨subd8_9_112, List.forall_mem_cons.2 ⟨subd8_9_113, List.forall_mem_cons.2 ⟨subd8_9_114, List.forall_mem_cons.2 ⟨subd8_9_115, List.forall_mem_cons.2 ⟨subd8_9_116, List.forall_mem_cons.2 ⟨subd8_9_117, List.forall_mem_cons.2 ⟨subd8_9_118, List.forall_mem_cons.2 ⟨subd8_9_119, List.forall_mem_cons.2 ⟨subd8_9_120, List.forall_mem_cons.2 ⟨subd8_9_121, List.forall_mem_cons.2 ⟨subd8_9_122, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_10 : ldCheck G d8_10.U d8_10.ms ldd8_10 = true := by decide +kernel
theorem pre_okd8_10 : subPre G cell8 d8_10 = true := by decide +kernel
theorem subd8_10_0 : subd8_10 [-3] = true := by decide +kernel
theorem subd8_10_1 : subd8_10 [-2, -2] = true := by decide +kernel
theorem subd8_10_2 : subd8_10 [-2, -1] = true := by decide +kernel
theorem subd8_10_3 : subd8_10 [-2, 0] = true := by decide +kernel
theorem subd8_10_4 : subd8_10 [-2, 1] = true := by decide +kernel
theorem subd8_10_5 : subd8_10 [-2, 2] = true := by decide +kernel
theorem subd8_10_6 : subd8_10 [-2, 3] = true := by decide +kernel
theorem subd8_10_7 : subd8_10 [-1, -3] = true := by decide +kernel
theorem subd8_10_8 : subd8_10 [-1, -2] = true := by decide +kernel
theorem subd8_10_9 : subd8_10 [-1, -1] = true := by decide +kernel
theorem subd8_10_10 : subd8_10 [-1, 0] = true := by decide +kernel
theorem subd8_10_11 : subd8_10 [-1, 1] = true := by decide +kernel
theorem subd8_10_12 : subd8_10 [-1, 2] = true := by decide +kernel
theorem subd8_10_13 : subd8_10 [-1, 3] = true := by decide +kernel
theorem subd8_10_14 : subd8_10 [0, -4] = true := by decide +kernel
theorem subd8_10_15 : subd8_10 [0, -3] = true := by decide +kernel
theorem subd8_10_16 : subd8_10 [0, -2] = true := by decide +kernel
theorem subd8_10_17 : subd8_10 [0, -1] = true := by decide +kernel
theorem subd8_10_18 : subd8_10 [0, 0, -7] = true := by decide +kernel
theorem subd8_10_19 : subd8_10 [0, 0, -6] = true := by decide +kernel
theorem subd8_10_20 : subd8_10 [0, 0, -5] = true := by decide +kernel
theorem subd8_10_21 : subd8_10 [0, 0, -4] = true := by decide +kernel
theorem subd8_10_22 : subd8_10 [0, 0, -3] = true := by decide +kernel
theorem subd8_10_23 : subd8_10 [0, 0, -2] = true := by decide +kernel
theorem subd8_10_24 : subd8_10 [0, 0, -1] = true := by decide +kernel
theorem subd8_10_25 : subd8_10 [0, 0, 0] = true := by decide +kernel
theorem subd8_10_26 : subd8_10 [0, 0, 1] = true := by decide +kernel
theorem subd8_10_27 : subd8_10 [0, 0, 2] = true := by decide +kernel
theorem subd8_10_28 : subd8_10 [0, 0, 3] = true := by decide +kernel
theorem subd8_10_29 : subd8_10 [0, 0, 4] = true := by decide +kernel
theorem subd8_10_30 : subd8_10 [0, 0, 5] = true := by decide +kernel
theorem subd8_10_31 : subd8_10 [0, 0, 6] = true := by decide +kernel
theorem sbd8_10_0 : ∀ q ∈ blkd8_10_0, subd8_10 q = true := by
  unfold blkd8_10_0
  exact List.forall_mem_cons.2 ⟨subd8_10_0, List.forall_mem_cons.2 ⟨subd8_10_1, List.forall_mem_cons.2 ⟨subd8_10_2, List.forall_mem_cons.2 ⟨subd8_10_3, List.forall_mem_cons.2 ⟨subd8_10_4, List.forall_mem_cons.2 ⟨subd8_10_5, List.forall_mem_cons.2 ⟨subd8_10_6, List.forall_mem_cons.2 ⟨subd8_10_7, List.forall_mem_cons.2 ⟨subd8_10_8, List.forall_mem_cons.2 ⟨subd8_10_9, List.forall_mem_cons.2 ⟨subd8_10_10, List.forall_mem_cons.2 ⟨subd8_10_11, List.forall_mem_cons.2 ⟨subd8_10_12, List.forall_mem_cons.2 ⟨subd8_10_13, List.forall_mem_cons.2 ⟨subd8_10_14, List.forall_mem_cons.2 ⟨subd8_10_15, List.forall_mem_cons.2 ⟨subd8_10_16, List.forall_mem_cons.2 ⟨subd8_10_17, List.forall_mem_cons.2 ⟨subd8_10_18, List.forall_mem_cons.2 ⟨subd8_10_19, List.forall_mem_cons.2 ⟨subd8_10_20, List.forall_mem_cons.2 ⟨subd8_10_21, List.forall_mem_cons.2 ⟨subd8_10_22, List.forall_mem_cons.2 ⟨subd8_10_23, List.forall_mem_cons.2 ⟨subd8_10_24, List.forall_mem_cons.2 ⟨subd8_10_25, List.forall_mem_cons.2 ⟨subd8_10_26, List.forall_mem_cons.2 ⟨subd8_10_27, List.forall_mem_cons.2 ⟨subd8_10_28, List.forall_mem_cons.2 ⟨subd8_10_29, List.forall_mem_cons.2 ⟨subd8_10_30, List.forall_mem_cons.2 ⟨subd8_10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
