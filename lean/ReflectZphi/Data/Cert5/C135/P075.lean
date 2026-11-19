import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_4_160 : subd11_4 [1, 2] = true := by decide +kernel
theorem subd11_4_161 : subd11_4 [1, 3] = true := by decide +kernel
theorem subd11_4_162 : subd11_4 [2, -4] = true := by decide +kernel
theorem subd11_4_163 : subd11_4 [2, -3] = true := by decide +kernel
theorem subd11_4_164 : subd11_4 [2, -2] = true := by decide +kernel
theorem subd11_4_165 : subd11_4 [2, -1] = true := by decide +kernel
theorem subd11_4_166 : subd11_4 [2, 0] = true := by decide +kernel
theorem subd11_4_167 : subd11_4 [2, 1] = true := by decide +kernel
theorem subd11_4_168 : subd11_4 [2, 2] = true := by decide +kernel
theorem subd11_4_169 : subd11_4 [2, 3] = true := by decide +kernel
theorem subd11_4_170 : subd11_4 [3, -3] = true := by decide +kernel
theorem subd11_4_171 : subd11_4 [3, -2] = true := by decide +kernel
theorem subd11_4_172 : subd11_4 [3, -1] = true := by decide +kernel
theorem subd11_4_173 : subd11_4 [3, 0] = true := by decide +kernel
theorem subd11_4_174 : subd11_4 [3, 1] = true := by decide +kernel
theorem subd11_4_175 : subd11_4 [3, 2] = true := by decide +kernel
theorem subd11_4_176 : subd11_4 [4] = true := by decide +kernel
theorem sbd11_4_5 : ∀ q ∈ blkd11_4_5, subd11_4 q = true := by
  unfold blkd11_4_5
  exact List.forall_mem_cons.2 ⟨subd11_4_160, List.forall_mem_cons.2 ⟨subd11_4_161, List.forall_mem_cons.2 ⟨subd11_4_162, List.forall_mem_cons.2 ⟨subd11_4_163, List.forall_mem_cons.2 ⟨subd11_4_164, List.forall_mem_cons.2 ⟨subd11_4_165, List.forall_mem_cons.2 ⟨subd11_4_166, List.forall_mem_cons.2 ⟨subd11_4_167, List.forall_mem_cons.2 ⟨subd11_4_168, List.forall_mem_cons.2 ⟨subd11_4_169, List.forall_mem_cons.2 ⟨subd11_4_170, List.forall_mem_cons.2 ⟨subd11_4_171, List.forall_mem_cons.2 ⟨subd11_4_172, List.forall_mem_cons.2 ⟨subd11_4_173, List.forall_mem_cons.2 ⟨subd11_4_174, List.forall_mem_cons.2 ⟨subd11_4_175, List.forall_mem_cons.2 ⟨subd11_4_176, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_5 : ldCheck G d11_5.U d11_5.ms ldd11_5 = true := by decide +kernel
theorem pre_okd11_5 : subPre G cell11 d11_5 = true := by decide +kernel
theorem subd11_5_0 : subd11_5 [-2, -4] = true := by decide +kernel
theorem subd11_5_1 : subd11_5 [-2, -3] = true := by decide +kernel
theorem subd11_5_2 : subd11_5 [-2, -2] = true := by decide +kernel
theorem subd11_5_3 : subd11_5 [-2, -1] = true := by decide +kernel
theorem subd11_5_4 : subd11_5 [-2, 0] = true := by decide +kernel
theorem subd11_5_5 : subd11_5 [-2, 1] = true := by decide +kernel
theorem subd11_5_6 : subd11_5 [-1, -4] = true := by decide +kernel
theorem subd11_5_7 : subd11_5 [-1, -3] = true := by decide +kernel
theorem subd11_5_8 : subd11_5 [-1, -2, -8] = true := by decide +kernel
theorem subd11_5_9 : subd11_5 [-1, -2, -7] = true := by decide +kernel
theorem subd11_5_10 : subd11_5 [-1, -2, -6] = true := by decide +kernel
theorem subd11_5_11 : subd11_5 [-1, -2, -5] = true := by decide +kernel
theorem subd11_5_12 : subd11_5 [-1, -2, -4] = true := by decide +kernel
theorem subd11_5_13 : subd11_5 [-1, -2, -3] = true := by decide +kernel
theorem subd11_5_14 : subd11_5 [-1, -2, -2] = true := by decide +kernel
theorem subd11_5_15 : subd11_5 [-1, -2, -1] = true := by decide +kernel
theorem subd11_5_16 : subd11_5 [-1, -2, 0] = true := by decide +kernel
theorem subd11_5_17 : subd11_5 [-1, -2, 1] = true := by decide +kernel
theorem subd11_5_18 : subd11_5 [-1, -2, 2] = true := by decide +kernel
theorem subd11_5_19 : subd11_5 [-1, -2, 3] = true := by decide +kernel
theorem subd11_5_20 : subd11_5 [-1, -2, 4] = true := by decide +kernel
theorem subd11_5_21 : subd11_5 [-1, -2, 5] = true := by decide +kernel
theorem subd11_5_22 : subd11_5 [-1, -1, -8] = true := by decide +kernel
theorem subd11_5_23 : subd11_5 [-1, -1, -7] = true := by decide +kernel
theorem subd11_5_24 : subd11_5 [-1, -1, -6] = true := by decide +kernel
theorem subd11_5_25 : subd11_5 [-1, -1, -5] = true := by decide +kernel
theorem subd11_5_26 : subd11_5 [-1, -1, -4] = true := by decide +kernel
theorem subd11_5_27 : subd11_5 [-1, -1, -3] = true := by decide +kernel
theorem subd11_5_28 : subd11_5 [-1, -1, -2] = true := by decide +kernel
theorem subd11_5_29 : subd11_5 [-1, -1, -1] = true := by decide +kernel
theorem subd11_5_30 : subd11_5 [-1, -1, 0] = true := by decide +kernel
theorem subd11_5_31 : subd11_5 [-1, -1, 1] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_cons.2 ⟨subd11_5_1, List.forall_mem_cons.2 ⟨subd11_5_2, List.forall_mem_cons.2 ⟨subd11_5_3, List.forall_mem_cons.2 ⟨subd11_5_4, List.forall_mem_cons.2 ⟨subd11_5_5, List.forall_mem_cons.2 ⟨subd11_5_6, List.forall_mem_cons.2 ⟨subd11_5_7, List.forall_mem_cons.2 ⟨subd11_5_8, List.forall_mem_cons.2 ⟨subd11_5_9, List.forall_mem_cons.2 ⟨subd11_5_10, List.forall_mem_cons.2 ⟨subd11_5_11, List.forall_mem_cons.2 ⟨subd11_5_12, List.forall_mem_cons.2 ⟨subd11_5_13, List.forall_mem_cons.2 ⟨subd11_5_14, List.forall_mem_cons.2 ⟨subd11_5_15, List.forall_mem_cons.2 ⟨subd11_5_16, List.forall_mem_cons.2 ⟨subd11_5_17, List.forall_mem_cons.2 ⟨subd11_5_18, List.forall_mem_cons.2 ⟨subd11_5_19, List.forall_mem_cons.2 ⟨subd11_5_20, List.forall_mem_cons.2 ⟨subd11_5_21, List.forall_mem_cons.2 ⟨subd11_5_22, List.forall_mem_cons.2 ⟨subd11_5_23, List.forall_mem_cons.2 ⟨subd11_5_24, List.forall_mem_cons.2 ⟨subd11_5_25, List.forall_mem_cons.2 ⟨subd11_5_26, List.forall_mem_cons.2 ⟨subd11_5_27, List.forall_mem_cons.2 ⟨subd11_5_28, List.forall_mem_cons.2 ⟨subd11_5_29, List.forall_mem_cons.2 ⟨subd11_5_30, List.forall_mem_cons.2 ⟨subd11_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_32 : subd11_5 [-1, -1, 2] = true := by decide +kernel
theorem subd11_5_33 : subd11_5 [-1, -1, 3] = true := by decide +kernel
theorem subd11_5_34 : subd11_5 [-1, -1, 4] = true := by decide +kernel
theorem subd11_5_35 : subd11_5 [-1, -1, 5] = true := by decide +kernel
theorem subd11_5_36 : subd11_5 [-1, -1, 6] = true := by decide +kernel
theorem subd11_5_37 : subd11_5 [-1, -1, 7] = true := by decide +kernel
theorem subd11_5_38 : subd11_5 [-1, 0, -8] = true := by decide +kernel
theorem subd11_5_39 : subd11_5 [-1, 0, -7] = true := by decide +kernel
theorem subd11_5_40 : subd11_5 [-1, 0, -6] = true := by decide +kernel
theorem subd11_5_41 : subd11_5 [-1, 0, -5] = true := by decide +kernel
theorem subd11_5_42 : subd11_5 [-1, 0, -4] = true := by decide +kernel
theorem subd11_5_43 : subd11_5 [-1, 0, -3] = true := by decide +kernel
theorem subd11_5_44 : subd11_5 [-1, 0, -2] = true := by decide +kernel
theorem subd11_5_45 : subd11_5 [-1, 0, -1] = true := by decide +kernel
theorem subd11_5_46 : subd11_5 [-1, 0, 0] = true := by decide +kernel
theorem subd11_5_47 : subd11_5 [-1, 0, 1] = true := by decide +kernel
theorem subd11_5_48 : subd11_5 [-1, 0, 2] = true := by decide +kernel
theorem subd11_5_49 : subd11_5 [-1, 0, 3] = true := by decide +kernel
theorem subd11_5_50 : subd11_5 [-1, 0, 4] = true := by decide +kernel
theorem subd11_5_51 : subd11_5 [-1, 0, 5] = true := by decide +kernel
theorem subd11_5_52 : subd11_5 [-1, 0, 6] = true := by decide +kernel
theorem subd11_5_53 : subd11_5 [-1, 0, 7] = true := by decide +kernel
theorem subd11_5_54 : subd11_5 [-1, 1, -6] = true := by decide +kernel
theorem subd11_5_55 : subd11_5 [-1, 1, -5] = true := by decide +kernel
theorem subd11_5_56 : subd11_5 [-1, 1, -4] = true := by decide +kernel
theorem subd11_5_57 : subd11_5 [-1, 1, -3] = true := by decide +kernel
theorem subd11_5_58 : subd11_5 [-1, 1, -2] = true := by decide +kernel
theorem subd11_5_59 : subd11_5 [-1, 1, -1] = true := by decide +kernel
theorem subd11_5_60 : subd11_5 [-1, 1, 0] = true := by decide +kernel
theorem subd11_5_61 : subd11_5 [-1, 1, 1] = true := by decide +kernel
theorem subd11_5_62 : subd11_5 [-1, 1, 2] = true := by decide +kernel
theorem subd11_5_63 : subd11_5 [-1, 1, 3] = true := by decide +kernel
theorem sbd11_5_1 : ∀ q ∈ blkd11_5_1, subd11_5 q = true := by
  unfold blkd11_5_1
  exact List.forall_mem_cons.2 ⟨subd11_5_32, List.forall_mem_cons.2 ⟨subd11_5_33, List.forall_mem_cons.2 ⟨subd11_5_34, List.forall_mem_cons.2 ⟨subd11_5_35, List.forall_mem_cons.2 ⟨subd11_5_36, List.forall_mem_cons.2 ⟨subd11_5_37, List.forall_mem_cons.2 ⟨subd11_5_38, List.forall_mem_cons.2 ⟨subd11_5_39, List.forall_mem_cons.2 ⟨subd11_5_40, List.forall_mem_cons.2 ⟨subd11_5_41, List.forall_mem_cons.2 ⟨subd11_5_42, List.forall_mem_cons.2 ⟨subd11_5_43, List.forall_mem_cons.2 ⟨subd11_5_44, List.forall_mem_cons.2 ⟨subd11_5_45, List.forall_mem_cons.2 ⟨subd11_5_46, List.forall_mem_cons.2 ⟨subd11_5_47, List.forall_mem_cons.2 ⟨subd11_5_48, List.forall_mem_cons.2 ⟨subd11_5_49, List.forall_mem_cons.2 ⟨subd11_5_50, List.forall_mem_cons.2 ⟨subd11_5_51, List.forall_mem_cons.2 ⟨subd11_5_52, List.forall_mem_cons.2 ⟨subd11_5_53, List.forall_mem_cons.2 ⟨subd11_5_54, List.forall_mem_cons.2 ⟨subd11_5_55, List.forall_mem_cons.2 ⟨subd11_5_56, List.forall_mem_cons.2 ⟨subd11_5_57, List.forall_mem_cons.2 ⟨subd11_5_58, List.forall_mem_cons.2 ⟨subd11_5_59, List.forall_mem_cons.2 ⟨subd11_5_60, List.forall_mem_cons.2 ⟨subd11_5_61, List.forall_mem_cons.2 ⟨subd11_5_62, List.forall_mem_cons.2 ⟨subd11_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_64 : subd11_5 [-1, 1, 4] = true := by decide +kernel
theorem subd11_5_65 : subd11_5 [-1, 1, 5] = true := by decide +kernel
theorem subd11_5_66 : subd11_5 [-1, 1, 6] = true := by decide +kernel
theorem subd11_5_67 : subd11_5 [-1, 2] = true := by decide +kernel
theorem subd11_5_68 : subd11_5 [0, -4] = true := by decide +kernel
theorem subd11_5_69 : subd11_5 [0, -3] = true := by decide +kernel
theorem subd11_5_70 : subd11_5 [0, -2] = true := by decide +kernel
theorem subd11_5_71 : subd11_5 [0, -1, -9] = true := by decide +kernel
theorem subd11_5_72 : subd11_5 [0, -1, -8] = true := by decide +kernel
theorem subd11_5_73 : subd11_5 [0, -1, -7] = true := by decide +kernel
theorem subd11_5_74 : subd11_5 [0, -1, -6] = true := by decide +kernel
theorem subd11_5_75 : subd11_5 [0, -1, -5] = true := by decide +kernel
theorem subd11_5_76 : subd11_5 [0, -1, -4] = true := by decide +kernel
theorem subd11_5_77 : subd11_5 [0, -1, -3] = true := by decide +kernel
theorem subd11_5_78 : subd11_5 [0, -1, -2] = true := by decide +kernel
theorem subd11_5_79 : subd11_5 [0, -1, -1] = true := by decide +kernel
theorem subd11_5_80 : subd11_5 [0, -1, 0] = true := by decide +kernel
theorem subd11_5_81 : subd11_5 [0, -1, 1] = true := by decide +kernel
theorem subd11_5_82 : subd11_5 [0, -1, 2] = true := by decide +kernel
theorem subd11_5_83 : subd11_5 [0, -1, 3] = true := by decide +kernel
theorem subd11_5_84 : subd11_5 [0, -1, 4] = true := by decide +kernel
theorem subd11_5_85 : subd11_5 [0, -1, 5] = true := by decide +kernel
theorem subd11_5_86 : subd11_5 [0, -1, 6] = true := by decide +kernel
theorem subd11_5_87 : subd11_5 [0, -1, 7] = true := by decide +kernel
theorem subd11_5_88 : subd11_5 [0, 0, -9] = true := by decide +kernel
theorem subd11_5_89 : subd11_5 [0, 0, -8] = true := by decide +kernel
theorem subd11_5_90 : subd11_5 [0, 0, -7] = true := by decide +kernel
theorem subd11_5_91 : subd11_5 [0, 0, -6] = true := by decide +kernel
theorem subd11_5_92 : subd11_5 [0, 0, -5] = true := by decide +kernel
theorem subd11_5_93 : subd11_5 [0, 0, -4] = true := by decide +kernel
theorem subd11_5_94 : subd11_5 [0, 0, -3] = true := by decide +kernel
theorem subd11_5_95 : subd11_5 [0, 0, -2] = true := by decide +kernel
theorem sbd11_5_2 : ∀ q ∈ blkd11_5_2, subd11_5 q = true := by
  unfold blkd11_5_2
  exact List.forall_mem_cons.2 ⟨subd11_5_64, List.forall_mem_cons.2 ⟨subd11_5_65, List.forall_mem_cons.2 ⟨subd11_5_66, List.forall_mem_cons.2 ⟨subd11_5_67, List.forall_mem_cons.2 ⟨subd11_5_68, List.forall_mem_cons.2 ⟨subd11_5_69, List.forall_mem_cons.2 ⟨subd11_5_70, List.forall_mem_cons.2 ⟨subd11_5_71, List.forall_mem_cons.2 ⟨subd11_5_72, List.forall_mem_cons.2 ⟨subd11_5_73, List.forall_mem_cons.2 ⟨subd11_5_74, List.forall_mem_cons.2 ⟨subd11_5_75, List.forall_mem_cons.2 ⟨subd11_5_76, List.forall_mem_cons.2 ⟨subd11_5_77, List.forall_mem_cons.2 ⟨subd11_5_78, List.forall_mem_cons.2 ⟨subd11_5_79, List.forall_mem_cons.2 ⟨subd11_5_80, List.forall_mem_cons.2 ⟨subd11_5_81, List.forall_mem_cons.2 ⟨subd11_5_82, List.forall_mem_cons.2 ⟨subd11_5_83, List.forall_mem_cons.2 ⟨subd11_5_84, List.forall_mem_cons.2 ⟨subd11_5_85, List.forall_mem_cons.2 ⟨subd11_5_86, List.forall_mem_cons.2 ⟨subd11_5_87, List.forall_mem_cons.2 ⟨subd11_5_88, List.forall_mem_cons.2 ⟨subd11_5_89, List.forall_mem_cons.2 ⟨subd11_5_90, List.forall_mem_cons.2 ⟨subd11_5_91, List.forall_mem_cons.2 ⟨subd11_5_92, List.forall_mem_cons.2 ⟨subd11_5_93, List.forall_mem_cons.2 ⟨subd11_5_94, List.forall_mem_cons.2 ⟨subd11_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_96 : subd11_5 [0, 0, -1] = true := by decide +kernel
theorem subd11_5_97 : subd11_5 [0, 0, 0] = true := by decide +kernel
theorem subd11_5_98 : subd11_5 [0, 0, 1] = true := by decide +kernel
theorem subd11_5_99 : subd11_5 [0, 0, 2] = true := by decide +kernel
theorem subd11_5_100 : subd11_5 [0, 0, 3] = true := by decide +kernel
theorem subd11_5_101 : subd11_5 [0, 0, 4] = true := by decide +kernel
theorem subd11_5_102 : subd11_5 [0, 0, 5] = true := by decide +kernel
theorem subd11_5_103 : subd11_5 [0, 0, 6] = true := by decide +kernel
theorem subd11_5_104 : subd11_5 [0, 0, 7] = true := by decide +kernel
theorem subd11_5_105 : subd11_5 [0, 0, 8] = true := by decide +kernel
theorem subd11_5_106 : subd11_5 [0, 1, -8] = true := by decide +kernel
theorem subd11_5_107 : subd11_5 [0, 1, -7] = true := by decide +kernel
theorem subd11_5_108 : subd11_5 [0, 1, -6] = true := by decide +kernel
theorem subd11_5_109 : subd11_5 [0, 1, -5] = true := by decide +kernel
theorem subd11_5_110 : subd11_5 [0, 1, -4] = true := by decide +kernel
theorem subd11_5_111 : subd11_5 [0, 1, -3] = true := by decide +kernel
theorem subd11_5_112 : subd11_5 [0, 1, -2] = true := by decide +kernel
theorem subd11_5_113 : subd11_5 [0, 1, -1] = true := by decide +kernel
theorem subd11_5_114 : subd11_5 [0, 1, 0] = true := by decide +kernel
theorem subd11_5_115 : subd11_5 [0, 1, 1] = true := by decide +kernel
theorem subd11_5_116 : subd11_5 [0, 1, 2] = true := by decide +kernel
theorem subd11_5_117 : subd11_5 [0, 1, 3] = true := by decide +kernel
theorem subd11_5_118 : subd11_5 [0, 1, 4] = true := by decide +kernel
theorem subd11_5_119 : subd11_5 [0, 1, 5] = true := by decide +kernel
theorem subd11_5_120 : subd11_5 [0, 1, 6] = true := by decide +kernel
theorem subd11_5_121 : subd11_5 [0, 1, 7] = true := by decide +kernel
theorem subd11_5_122 : subd11_5 [0, 1, 8] = true := by decide +kernel
theorem subd11_5_123 : subd11_5 [0, 2] = true := by decide +kernel
theorem subd11_5_124 : subd11_5 [0, 3] = true := by decide +kernel
theorem subd11_5_125 : subd11_5 [1, -3] = true := by decide +kernel
theorem subd11_5_126 : subd11_5 [1, -2] = true := by decide +kernel
theorem subd11_5_127 : subd11_5 [1, -1, -7] = true := by decide +kernel
theorem sbd11_5_3 : ∀ q ∈ blkd11_5_3, subd11_5 q = true := by
  unfold blkd11_5_3
  exact List.forall_mem_cons.2 ⟨subd11_5_96, List.forall_mem_cons.2 ⟨subd11_5_97, List.forall_mem_cons.2 ⟨subd11_5_98, List.forall_mem_cons.2 ⟨subd11_5_99, List.forall_mem_cons.2 ⟨subd11_5_100, List.forall_mem_cons.2 ⟨subd11_5_101, List.forall_mem_cons.2 ⟨subd11_5_102, List.forall_mem_cons.2 ⟨subd11_5_103, List.forall_mem_cons.2 ⟨subd11_5_104, List.forall_mem_cons.2 ⟨subd11_5_105, List.forall_mem_cons.2 ⟨subd11_5_106, List.forall_mem_cons.2 ⟨subd11_5_107, List.forall_mem_cons.2 ⟨subd11_5_108, List.forall_mem_cons.2 ⟨subd11_5_109, List.forall_mem_cons.2 ⟨subd11_5_110, List.forall_mem_cons.2 ⟨subd11_5_111, List.forall_mem_cons.2 ⟨subd11_5_112, List.forall_mem_cons.2 ⟨subd11_5_113, List.forall_mem_cons.2 ⟨subd11_5_114, List.forall_mem_cons.2 ⟨subd11_5_115, List.forall_mem_cons.2 ⟨subd11_5_116, List.forall_mem_cons.2 ⟨subd11_5_117, List.forall_mem_cons.2 ⟨subd11_5_118, List.forall_mem_cons.2 ⟨subd11_5_119, List.forall_mem_cons.2 ⟨subd11_5_120, List.forall_mem_cons.2 ⟨subd11_5_121, List.forall_mem_cons.2 ⟨subd11_5_122, List.forall_mem_cons.2 ⟨subd11_5_123, List.forall_mem_cons.2 ⟨subd11_5_124, List.forall_mem_cons.2 ⟨subd11_5_125, List.forall_mem_cons.2 ⟨subd11_5_126, List.forall_mem_cons.2 ⟨subd11_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_128 : subd11_5 [1, -1, -6] = true := by decide +kernel
theorem subd11_5_129 : subd11_5 [1, -1, -5] = true := by decide +kernel
theorem subd11_5_130 : subd11_5 [1, -1, -4] = true := by decide +kernel
theorem subd11_5_131 : subd11_5 [1, -1, -3] = true := by decide +kernel
theorem subd11_5_132 : subd11_5 [1, -1, -2] = true := by decide +kernel
theorem subd11_5_133 : subd11_5 [1, -1, -1] = true := by decide +kernel
theorem subd11_5_134 : subd11_5 [1, -1, 0] = true := by decide +kernel
theorem subd11_5_135 : subd11_5 [1, -1, 1] = true := by decide +kernel
theorem subd11_5_136 : subd11_5 [1, -1, 2] = true := by decide +kernel
theorem subd11_5_137 : subd11_5 [1, -1, 3] = true := by decide +kernel
theorem subd11_5_138 : subd11_5 [1, -1, 4] = true := by decide +kernel
theorem subd11_5_139 : subd11_5 [1, -1, 5] = true := by decide +kernel
theorem subd11_5_140 : subd11_5 [1, 0, -8] = true := by decide +kernel
theorem subd11_5_141 : subd11_5 [1, 0, -7] = true := by decide +kernel
theorem subd11_5_142 : subd11_5 [1, 0, -6] = true := by decide +kernel
theorem subd11_5_143 : subd11_5 [1, 0, -5] = true := by decide +kernel
theorem subd11_5_144 : subd11_5 [1, 0, -4] = true := by decide +kernel
theorem subd11_5_145 : subd11_5 [1, 0, -3] = true := by decide +kernel
theorem subd11_5_146 : subd11_5 [1, 0, -2] = true := by decide +kernel
theorem subd11_5_147 : subd11_5 [1, 0, -1] = true := by decide +kernel
theorem subd11_5_148 : subd11_5 [1, 0, 0] = true := by decide +kernel
theorem subd11_5_149 : subd11_5 [1, 0, 1] = true := by decide +kernel
theorem subd11_5_150 : subd11_5 [1, 0, 2] = true := by decide +kernel
theorem subd11_5_151 : subd11_5 [1, 0, 3] = true := by decide +kernel
theorem subd11_5_152 : subd11_5 [1, 0, 4] = true := by decide +kernel
theorem subd11_5_153 : subd11_5 [1, 0, 5] = true := by decide +kernel
theorem subd11_5_154 : subd11_5 [1, 0, 6] = true := by decide +kernel
theorem subd11_5_155 : subd11_5 [1, 0, 7] = true := by decide +kernel
theorem subd11_5_156 : subd11_5 [1, 1, -8] = true := by decide +kernel
theorem subd11_5_157 : subd11_5 [1, 1, -7] = true := by decide +kernel
theorem subd11_5_158 : subd11_5 [1, 1, -6] = true := by decide +kernel
theorem subd11_5_159 : subd11_5 [1, 1, -5] = true := by decide +kernel
theorem sbd11_5_4 : ∀ q ∈ blkd11_5_4, subd11_5 q = true := by
  unfold blkd11_5_4
  exact List.forall_mem_cons.2 ⟨subd11_5_128, List.forall_mem_cons.2 ⟨subd11_5_129, List.forall_mem_cons.2 ⟨subd11_5_130, List.forall_mem_cons.2 ⟨subd11_5_131, List.forall_mem_cons.2 ⟨subd11_5_132, List.forall_mem_cons.2 ⟨subd11_5_133, List.forall_mem_cons.2 ⟨subd11_5_134, List.forall_mem_cons.2 ⟨subd11_5_135, List.forall_mem_cons.2 ⟨subd11_5_136, List.forall_mem_cons.2 ⟨subd11_5_137, List.forall_mem_cons.2 ⟨subd11_5_138, List.forall_mem_cons.2 ⟨subd11_5_139, List.forall_mem_cons.2 ⟨subd11_5_140, List.forall_mem_cons.2 ⟨subd11_5_141, List.forall_mem_cons.2 ⟨subd11_5_142, List.forall_mem_cons.2 ⟨subd11_5_143, List.forall_mem_cons.2 ⟨subd11_5_144, List.forall_mem_cons.2 ⟨subd11_5_145, List.forall_mem_cons.2 ⟨subd11_5_146, List.forall_mem_cons.2 ⟨subd11_5_147, List.forall_mem_cons.2 ⟨subd11_5_148, List.forall_mem_cons.2 ⟨subd11_5_149, List.forall_mem_cons.2 ⟨subd11_5_150, List.forall_mem_cons.2 ⟨subd11_5_151, List.forall_mem_cons.2 ⟨subd11_5_152, List.forall_mem_cons.2 ⟨subd11_5_153, List.forall_mem_cons.2 ⟨subd11_5_154, List.forall_mem_cons.2 ⟨subd11_5_155, List.forall_mem_cons.2 ⟨subd11_5_156, List.forall_mem_cons.2 ⟨subd11_5_157, List.forall_mem_cons.2 ⟨subd11_5_158, List.forall_mem_cons.2 ⟨subd11_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_160 : subd11_5 [1, 1, -4] = true := by decide +kernel
theorem subd11_5_161 : subd11_5 [1, 1, -3] = true := by decide +kernel
theorem subd11_5_162 : subd11_5 [1, 1, -2] = true := by decide +kernel
theorem subd11_5_163 : subd11_5 [1, 1, -1] = true := by decide +kernel
theorem subd11_5_164 : subd11_5 [1, 1, 0] = true := by decide +kernel
theorem subd11_5_165 : subd11_5 [1, 1, 1] = true := by decide +kernel
theorem subd11_5_166 : subd11_5 [1, 1, 2] = true := by decide +kernel
theorem subd11_5_167 : subd11_5 [1, 1, 3] = true := by decide +kernel
theorem subd11_5_168 : subd11_5 [1, 1, 4] = true := by decide +kernel
theorem subd11_5_169 : subd11_5 [1, 1, 5] = true := by decide +kernel
theorem subd11_5_170 : subd11_5 [1, 1, 6] = true := by decide +kernel
theorem subd11_5_171 : subd11_5 [1, 1, 7] = true := by decide +kernel
theorem subd11_5_172 : subd11_5 [1, 2, -6] = true := by decide +kernel
theorem subd11_5_173 : subd11_5 [1, 2, -5] = true := by decide +kernel
theorem subd11_5_174 : subd11_5 [1, 2, -4] = true := by decide +kernel
theorem subd11_5_175 : subd11_5 [1, 2, -3] = true := by decide +kernel
theorem subd11_5_176 : subd11_5 [1, 2, -2] = true := by decide +kernel
theorem subd11_5_177 : subd11_5 [1, 2, -1] = true := by decide +kernel
theorem subd11_5_178 : subd11_5 [1, 2, 0] = true := by decide +kernel
theorem subd11_5_179 : subd11_5 [1, 2, 1] = true := by decide +kernel
theorem subd11_5_180 : subd11_5 [1, 2, 2] = true := by decide +kernel
theorem subd11_5_181 : subd11_5 [1, 2, 3] = true := by decide +kernel
theorem subd11_5_182 : subd11_5 [1, 2, 4] = true := by decide +kernel
theorem subd11_5_183 : subd11_5 [1, 2, 5] = true := by decide +kernel
theorem subd11_5_184 : subd11_5 [1, 2, 6] = true := by decide +kernel
theorem subd11_5_185 : subd11_5 [1, 2, 7] = true := by decide +kernel
theorem subd11_5_186 : subd11_5 [1, 3] = true := by decide +kernel
theorem subd11_5_187 : subd11_5 [2, -2] = true := by decide +kernel
theorem subd11_5_188 : subd11_5 [2, -1] = true := by decide +kernel
theorem subd11_5_189 : subd11_5 [2, 0] = true := by decide +kernel
theorem subd11_5_190 : subd11_5 [2, 1] = true := by decide +kernel
theorem subd11_5_191 : subd11_5 [2, 2] = true := by decide +kernel
theorem sbd11_5_5 : ∀ q ∈ blkd11_5_5, subd11_5 q = true := by
  unfold blkd11_5_5
  exact List.forall_mem_cons.2 ⟨subd11_5_160, List.forall_mem_cons.2 ⟨subd11_5_161, List.forall_mem_cons.2 ⟨subd11_5_162, List.forall_mem_cons.2 ⟨subd11_5_163, List.forall_mem_cons.2 ⟨subd11_5_164, List.forall_mem_cons.2 ⟨subd11_5_165, List.forall_mem_cons.2 ⟨subd11_5_166, List.forall_mem_cons.2 ⟨subd11_5_167, List.forall_mem_cons.2 ⟨subd11_5_168, List.forall_mem_cons.2 ⟨subd11_5_169, List.forall_mem_cons.2 ⟨subd11_5_170, List.forall_mem_cons.2 ⟨subd11_5_171, List.forall_mem_cons.2 ⟨subd11_5_172, List.forall_mem_cons.2 ⟨subd11_5_173, List.forall_mem_cons.2 ⟨subd11_5_174, List.forall_mem_cons.2 ⟨subd11_5_175, List.forall_mem_cons.2 ⟨subd11_5_176, List.forall_mem_cons.2 ⟨subd11_5_177, List.forall_mem_cons.2 ⟨subd11_5_178, List.forall_mem_cons.2 ⟨subd11_5_179, List.forall_mem_cons.2 ⟨subd11_5_180, List.forall_mem_cons.2 ⟨subd11_5_181, List.forall_mem_cons.2 ⟨subd11_5_182, List.forall_mem_cons.2 ⟨subd11_5_183, List.forall_mem_cons.2 ⟨subd11_5_184, List.forall_mem_cons.2 ⟨subd11_5_185, List.forall_mem_cons.2 ⟨subd11_5_186, List.forall_mem_cons.2 ⟨subd11_5_187, List.forall_mem_cons.2 ⟨subd11_5_188, List.forall_mem_cons.2 ⟨subd11_5_189, List.forall_mem_cons.2 ⟨subd11_5_190, List.forall_mem_cons.2 ⟨subd11_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_5_192 : subd11_5 [2, 3] = true := by decide +kernel
theorem sbd11_5_6 : ∀ q ∈ blkd11_5_6, subd11_5 q = true := by
  unfold blkd11_5_6
  exact List.forall_mem_cons.2 ⟨subd11_5_192, List.forall_mem_nil _⟩
theorem ld_okd11_6 : ldCheck G d11_6.U d11_6.ms ldd11_6 = true := by decide +kernel
theorem pre_okd11_6 : subPre G cell11 d11_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
