import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_544 : sub8 [3, -1, 1] = true := by decide +kernel
theorem sub8_545 : sub8 [3, -1, 2] = true := by decide +kernel
theorem sub8_546 : sub8 [3, -1, 3] = true := by decide +kernel
theorem sub8_547 : sub8 [3, -1, 4] = true := by decide +kernel
theorem sub8_548 : sub8 [3, -1, 5] = true := by decide +kernel
theorem sub8_549 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_550 : sub8 [3, 1] = true := by decide +kernel
theorem sub8_551 : sub8 [3, 2] = true := by decide +kernel
theorem sub8_552 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_553 : sub8 [4, -7] = true := by decide +kernel
theorem sub8_554 : sub8 [4, -6] = true := by decide +kernel
theorem sub8_555 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_556 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_557 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_558 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_559 : sub8 [4, -1] = true := by decide +kernel
theorem sub8_560 : sub8 [4, 0] = true := by decide +kernel
theorem sub8_561 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_562 : sub8 [4, 2] = true := by decide +kernel
theorem sub8_563 : sub8 [5, -5] = true := by decide +kernel
theorem sub8_564 : sub8 [5, -4] = true := by decide +kernel
theorem sub8_565 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_566 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_567 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_568 : sub8 [5, 0] = true := by decide +kernel
theorem sb8_17 : ∀ q ∈ blk8_17, sub8 q = true := by
  unfold blk8_17
  exact List.forall_mem_cons.2 ⟨sub8_544, List.forall_mem_cons.2 ⟨sub8_545, List.forall_mem_cons.2 ⟨sub8_546, List.forall_mem_cons.2 ⟨sub8_547, List.forall_mem_cons.2 ⟨sub8_548, List.forall_mem_cons.2 ⟨sub8_549, List.forall_mem_cons.2 ⟨sub8_550, List.forall_mem_cons.2 ⟨sub8_551, List.forall_mem_cons.2 ⟨sub8_552, List.forall_mem_cons.2 ⟨sub8_553, List.forall_mem_cons.2 ⟨sub8_554, List.forall_mem_cons.2 ⟨sub8_555, List.forall_mem_cons.2 ⟨sub8_556, List.forall_mem_cons.2 ⟨sub8_557, List.forall_mem_cons.2 ⟨sub8_558, List.forall_mem_cons.2 ⟨sub8_559, List.forall_mem_cons.2 ⟨sub8_560, List.forall_mem_cons.2 ⟨sub8_561, List.forall_mem_cons.2 ⟨sub8_562, List.forall_mem_cons.2 ⟨sub8_563, List.forall_mem_cons.2 ⟨sub8_564, List.forall_mem_cons.2 ⟨sub8_565, List.forall_mem_cons.2 ⟨sub8_566, List.forall_mem_cons.2 ⟨sub8_567, List.forall_mem_cons.2 ⟨sub8_568, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-9] = true := by decide +kernel
theorem sub9_1 : sub9 [-8, -6] = true := by decide +kernel
theorem sub9_2 : sub9 [-8, -5] = true := by decide +kernel
theorem sub9_3 : sub9 [-8, -4] = true := by decide +kernel
theorem sub9_4 : sub9 [-8, -3] = true := by decide +kernel
theorem sub9_5 : sub9 [-8, -2] = true := by decide +kernel
theorem sub9_6 : sub9 [-8, -1] = true := by decide +kernel
theorem sub9_7 : sub9 [-8, 0] = true := by decide +kernel
theorem sub9_8 : sub9 [-8, 1] = true := by decide +kernel
theorem sub9_9 : sub9 [-8, 2] = true := by decide +kernel
theorem sub9_10 : sub9 [-7, -7] = true := by decide +kernel
theorem sub9_11 : sub9 [-7, -6] = true := by decide +kernel
theorem sub9_12 : sub9 [-7, -5] = true := by decide +kernel
theorem sub9_13 : sub9 [-7, -4] = true := by decide +kernel
theorem sub9_14 : sub9 [-7, -3] = true := by decide +kernel
theorem sub9_15 : sub9 [-7, -2] = true := by decide +kernel
theorem sub9_16 : sub9 [-7, -1] = true := by decide +kernel
theorem sub9_17 : sub9 [-7, 0] = true := by decide +kernel
theorem sub9_18 : sub9 [-7, 1] = true := by decide +kernel
theorem sub9_19 : sub9 [-7, 2] = true := by decide +kernel
theorem sub9_20 : sub9 [-7, 3] = true := by decide +kernel
theorem sub9_21 : sub9 [-6, -8] = true := by decide +kernel
theorem sub9_22 : sub9 [-6, -7] = true := by decide +kernel
theorem sub9_23 : sub9 [-6, -6] = true := by decide +kernel
theorem sub9_24 : sub9 [-6, -5] = true := by decide +kernel
theorem sub9_25 : sub9 [-6, -4] = true := by decide +kernel
theorem sub9_26 : sub9 [-6, -3] = true := by decide +kernel
theorem sub9_27 : sub9 [-6, -2] = true := by decide +kernel
theorem sub9_28 : sub9 [-6, -1] = true := by decide +kernel
theorem sub9_29 : sub9 [-6, 0] = true := by decide +kernel
theorem sub9_30 : sub9 [-6, 1] = true := by decide +kernel
theorem sub9_31 : sub9 [-6, 2] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [-6, 3] = true := by decide +kernel
theorem sub9_33 : sub9 [-6, 4] = true := by decide +kernel
theorem sub9_34 : sub9 [-5, -8] = true := by decide +kernel
theorem sub9_35 : sub9 [-5, -7] = true := by decide +kernel
theorem sub9_36 : sub9 [-5, -6] = true := by decide +kernel
theorem sub9_37 : sub9 [-5, -5] = true := by decide +kernel
theorem sub9_38 : sub9 [-5, -4] = true := by decide +kernel
theorem sub9_39 : sub9 [-5, -3] = true := by decide +kernel
theorem sub9_40 : sub9 [-5, -2] = true := by decide +kernel
theorem sub9_41 : sub9 [-5, -1] = true := by decide +kernel
theorem sub9_42 : sub9 [-5, 0] = true := by decide +kernel
theorem sub9_43 : sub9 [-5, 1] = true := by decide +kernel
theorem sub9_44 : sub9 [-5, 2] = true := by decide +kernel
theorem sub9_45 : sub9 [-5, 3] = true := by decide +kernel
theorem sub9_46 : sub9 [-5, 4] = true := by decide +kernel
theorem sub9_47 : sub9 [-5, 5] = true := by decide +kernel
theorem sub9_48 : sub9 [-4, -8] = true := by decide +kernel
theorem sub9_49 : sub9 [-4, -7] = true := by decide +kernel
theorem sub9_50 : sub9 [-4, -6] = true := by decide +kernel
theorem sub9_51 : sub9 [-4, -5] = true := by decide +kernel
theorem sub9_52 : sub9 [-4, -4] = true := by decide +kernel
theorem sub9_53 : sub9 [-4, -3, -8] = true := by decide +kernel
theorem sub9_54 : sub9 [-4, -3, -7] = true := by decide +kernel
theorem sub9_55 : sub9 [-4, -3, -6] = true := by decide +kernel
theorem sub9_56 : sub9 [-4, -3, -5] = true := by decide +kernel
theorem sub9_57 : sub9 [-4, -3, -4] = true := by decide +kernel
theorem sub9_58 : sub9 [-4, -3, -3] = true := by decide +kernel
theorem sub9_59 : sub9 [-4, -3, -2] = true := by decide +kernel
theorem sub9_60 : sub9 [-4, -3, -1] = true := by decide +kernel
theorem sub9_61 : sub9 [-4, -3, 0] = true := by decide +kernel
theorem sub9_62 : sub9 [-4, -3, 1] = true := by decide +kernel
theorem sub9_63 : sub9 [-4, -3, 2] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [-4, -3, 3] = true := by decide +kernel
theorem sub9_65 : sub9 [-4, -3, 4] = true := by decide +kernel
theorem sub9_66 : sub9 [-4, -2, -8] = true := by decide +kernel
theorem sub9_67 : sub9 [-4, -2, -7] = true := by decide +kernel
theorem sub9_68 : sub9 [-4, -2, -6] = true := by decide +kernel
theorem sub9_69 : sub9 [-4, -2, -5] = true := by decide +kernel
theorem sub9_70 : sub9 [-4, -2, -4] = true := by decide +kernel
theorem sub9_71 : sub9 [-4, -2, -3] = true := by decide +kernel
theorem sub9_72 : sub9 [-4, -2, -2] = true := by decide +kernel
theorem sub9_73 : sub9 [-4, -2, -1] = true := by decide +kernel
theorem sub9_74 : sub9 [-4, -2, 0] = true := by decide +kernel
theorem sub9_75 : sub9 [-4, -2, 1] = true := by decide +kernel
theorem sub9_76 : sub9 [-4, -2, 2] = true := by decide +kernel
theorem sub9_77 : sub9 [-4, -2, 3] = true := by decide +kernel
theorem sub9_78 : sub9 [-4, -2, 4] = true := by decide +kernel
theorem sub9_79 : sub9 [-4, -2, 5] = true := by decide +kernel
theorem sub9_80 : sub9 [-4, -1, -8] = true := by decide +kernel
theorem sub9_81 : sub9 [-4, -1, -7] = true := by decide +kernel
theorem sub9_82 : sub9 [-4, -1, -6] = true := by decide +kernel
theorem sub9_83 : sub9 [-4, -1, -5] = true := by decide +kernel
theorem sub9_84 : sub9 [-4, -1, -4] = true := by decide +kernel
theorem sub9_85 : sub9 [-4, -1, -3] = true := by decide +kernel
theorem sub9_86 : sub9 [-4, -1, -2] = true := by decide +kernel
theorem sub9_87 : sub9 [-4, -1, -1] = true := by decide +kernel
theorem sub9_88 : sub9 [-4, -1, 0] = true := by decide +kernel
theorem sub9_89 : sub9 [-4, -1, 1] = true := by decide +kernel
theorem sub9_90 : sub9 [-4, -1, 2] = true := by decide +kernel
theorem sub9_91 : sub9 [-4, -1, 3] = true := by decide +kernel
theorem sub9_92 : sub9 [-4, -1, 4] = true := by decide +kernel
theorem sub9_93 : sub9 [-4, -1, 5] = true := by decide +kernel
theorem sub9_94 : sub9 [-4, 0, -8] = true := by decide +kernel
theorem sub9_95 : sub9 [-4, 0, -7] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_cons.2 ⟨sub9_72, List.forall_mem_cons.2 ⟨sub9_73, List.forall_mem_cons.2 ⟨sub9_74, List.forall_mem_cons.2 ⟨sub9_75, List.forall_mem_cons.2 ⟨sub9_76, List.forall_mem_cons.2 ⟨sub9_77, List.forall_mem_cons.2 ⟨sub9_78, List.forall_mem_cons.2 ⟨sub9_79, List.forall_mem_cons.2 ⟨sub9_80, List.forall_mem_cons.2 ⟨sub9_81, List.forall_mem_cons.2 ⟨sub9_82, List.forall_mem_cons.2 ⟨sub9_83, List.forall_mem_cons.2 ⟨sub9_84, List.forall_mem_cons.2 ⟨sub9_85, List.forall_mem_cons.2 ⟨sub9_86, List.forall_mem_cons.2 ⟨sub9_87, List.forall_mem_cons.2 ⟨sub9_88, List.forall_mem_cons.2 ⟨sub9_89, List.forall_mem_cons.2 ⟨sub9_90, List.forall_mem_cons.2 ⟨sub9_91, List.forall_mem_cons.2 ⟨sub9_92, List.forall_mem_cons.2 ⟨sub9_93, List.forall_mem_cons.2 ⟨sub9_94, List.forall_mem_cons.2 ⟨sub9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_96 : sub9 [-4, 0, -6] = true := by decide +kernel
theorem sub9_97 : sub9 [-4, 0, -5] = true := by decide +kernel
theorem sub9_98 : sub9 [-4, 0, -4] = true := by decide +kernel
theorem sub9_99 : sub9 [-4, 0, -3] = true := by decide +kernel
theorem sub9_100 : sub9 [-4, 0, -2] = true := by decide +kernel
theorem sub9_101 : sub9 [-4, 0, -1] = true := by decide +kernel
theorem sub9_102 : sub9 [-4, 0, 0] = true := by decide +kernel
theorem sub9_103 : sub9 [-4, 0, 1] = true := by decide +kernel
theorem sub9_104 : sub9 [-4, 0, 2] = true := by decide +kernel
theorem sub9_105 : sub9 [-4, 0, 3] = true := by decide +kernel
theorem sub9_106 : sub9 [-4, 0, 4] = true := by decide +kernel
theorem sub9_107 : sub9 [-4, 0, 5] = true := by decide +kernel
theorem sub9_108 : sub9 [-4, 1, -7] = true := by decide +kernel
theorem sub9_109 : sub9 [-4, 1, -6] = true := by decide +kernel
theorem sub9_110 : sub9 [-4, 1, -5] = true := by decide +kernel
theorem sub9_111 : sub9 [-4, 1, -4] = true := by decide +kernel
theorem sub9_112 : sub9 [-4, 1, -3] = true := by decide +kernel
theorem sub9_113 : sub9 [-4, 1, -2] = true := by decide +kernel
theorem sub9_114 : sub9 [-4, 1, -1] = true := by decide +kernel
theorem sub9_115 : sub9 [-4, 1, 0] = true := by decide +kernel
theorem sub9_116 : sub9 [-4, 1, 1] = true := by decide +kernel
theorem sub9_117 : sub9 [-4, 1, 2] = true := by decide +kernel
theorem sub9_118 : sub9 [-4, 1, 3] = true := by decide +kernel
theorem sub9_119 : sub9 [-4, 1, 4] = true := by decide +kernel
theorem sub9_120 : sub9 [-4, 1, 5] = true := by decide +kernel
theorem sub9_121 : sub9 [-4, 2] = true := by decide +kernel
theorem sub9_122 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_123 : sub9 [-4, 4] = true := by decide +kernel
theorem sub9_124 : sub9 [-4, 5] = true := by decide +kernel
theorem sub9_125 : sub9 [-4, 6] = true := by decide +kernel
theorem sub9_126 : sub9 [-3, -9] = true := by decide +kernel
theorem sub9_127 : sub9 [-3, -8] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [-3, -7] = true := by decide +kernel
theorem sub9_129 : sub9 [-3, -6] = true := by decide +kernel
theorem sub9_130 : sub9 [-3, -5] = true := by decide +kernel
theorem sub9_131 : sub9 [-3, -4, -8] = true := by decide +kernel
theorem sub9_132 : sub9 [-3, -4, -7] = true := by decide +kernel
theorem sub9_133 : sub9 [-3, -4, -6] = true := by decide +kernel
theorem sub9_134 : sub9 [-3, -4, -5] = true := by decide +kernel
theorem sub9_135 : sub9 [-3, -4, -4] = true := by decide +kernel
theorem sub9_136 : sub9 [-3, -4, -3] = true := by decide +kernel
theorem sub9_137 : sub9 [-3, -4, -2] = true := by decide +kernel
theorem sub9_138 : sub9 [-3, -4, -1] = true := by decide +kernel
theorem sub9_139 : sub9 [-3, -4, 0] = true := by decide +kernel
theorem sub9_140 : sub9 [-3, -4, 1] = true := by decide +kernel
theorem sub9_141 : sub9 [-3, -4, 2] = true := by decide +kernel
theorem sub9_142 : sub9 [-3, -4, 3] = true := by decide +kernel
theorem sub9_143 : sub9 [-3, -4, 4] = true := by decide +kernel
theorem sub9_144 : sub9 [-3, -3, -8] = true := by decide +kernel
theorem sub9_145 : sub9 [-3, -3, -7] = true := by decide +kernel
theorem sub9_146 : sub9 [-3, -3, -6] = true := by decide +kernel
theorem sub9_147 : sub9 [-3, -3, -5] = true := by decide +kernel
theorem sub9_148 : sub9 [-3, -3, -4] = true := by decide +kernel
theorem sub9_149 : sub9 [-3, -3, -3] = true := by decide +kernel
theorem sub9_150 : sub9 [-3, -3, -2] = true := by decide +kernel
theorem sub9_151 : sub9 [-3, -3, -1] = true := by decide +kernel
theorem sub9_152 : sub9 [-3, -3, 0] = true := by decide +kernel
theorem sub9_153 : sub9 [-3, -3, 1] = true := by decide +kernel
theorem sub9_154 : sub9 [-3, -3, 2] = true := by decide +kernel
theorem sub9_155 : sub9 [-3, -3, 3] = true := by decide +kernel
theorem sub9_156 : sub9 [-3, -3, 4] = true := by decide +kernel
theorem sub9_157 : sub9 [-3, -3, 5] = true := by decide +kernel
theorem sub9_158 : sub9 [-3, -2, -8] = true := by decide +kernel
theorem sub9_159 : sub9 [-3, -2, -7] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_160 : sub9 [-3, -2, -6] = true := by decide +kernel
theorem sub9_161 : sub9 [-3, -2, -5] = true := by decide +kernel
theorem sub9_162 : sub9 [-3, -2, -4] = true := by decide +kernel
theorem sub9_163 : sub9 [-3, -2, -3] = true := by decide +kernel
theorem sub9_164 : sub9 [-3, -2, -2] = true := by decide +kernel
theorem sub9_165 : sub9 [-3, -2, -1] = true := by decide +kernel
theorem sub9_166 : sub9 [-3, -2, 0] = true := by decide +kernel
theorem sub9_167 : sub9 [-3, -2, 1] = true := by decide +kernel
theorem sub9_168 : sub9 [-3, -2, 2] = true := by decide +kernel
theorem sub9_169 : sub9 [-3, -2, 3] = true := by decide +kernel
theorem sub9_170 : sub9 [-3, -2, 4] = true := by decide +kernel
theorem sub9_171 : sub9 [-3, -2, 5] = true := by decide +kernel
theorem sub9_172 : sub9 [-3, -1, -8] = true := by decide +kernel
theorem sub9_173 : sub9 [-3, -1, -7] = true := by decide +kernel
theorem sub9_174 : sub9 [-3, -1, -6] = true := by decide +kernel
theorem sub9_175 : sub9 [-3, -1, -5] = true := by decide +kernel
theorem sub9_176 : sub9 [-3, -1, -4] = true := by decide +kernel
theorem sub9_177 : sub9 [-3, -1, -3] = true := by decide +kernel
theorem sub9_178 : sub9 [-3, -1, -2] = true := by decide +kernel
theorem sub9_179 : sub9 [-3, -1, -1] = true := by decide +kernel
theorem sub9_180 : sub9 [-3, -1, 0] = true := by decide +kernel
theorem sub9_181 : sub9 [-3, -1, 1] = true := by decide +kernel
theorem sub9_182 : sub9 [-3, -1, 2] = true := by decide +kernel
theorem sub9_183 : sub9 [-3, -1, 3] = true := by decide +kernel
theorem sub9_184 : sub9 [-3, -1, 4] = true := by decide +kernel
theorem sub9_185 : sub9 [-3, -1, 5] = true := by decide +kernel
theorem sub9_186 : sub9 [-3, -1, 6] = true := by decide +kernel
theorem sub9_187 : sub9 [-3, 0, -8] = true := by decide +kernel
theorem sub9_188 : sub9 [-3, 0, -7] = true := by decide +kernel
theorem sub9_189 : sub9 [-3, 0, -6] = true := by decide +kernel
theorem sub9_190 : sub9 [-3, 0, -5] = true := by decide +kernel
theorem sub9_191 : sub9 [-3, 0, -4] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_cons.2 ⟨sub9_179, List.forall_mem_cons.2 ⟨sub9_180, List.forall_mem_cons.2 ⟨sub9_181, List.forall_mem_cons.2 ⟨sub9_182, List.forall_mem_cons.2 ⟨sub9_183, List.forall_mem_cons.2 ⟨sub9_184, List.forall_mem_cons.2 ⟨sub9_185, List.forall_mem_cons.2 ⟨sub9_186, List.forall_mem_cons.2 ⟨sub9_187, List.forall_mem_cons.2 ⟨sub9_188, List.forall_mem_cons.2 ⟨sub9_189, List.forall_mem_cons.2 ⟨sub9_190, List.forall_mem_cons.2 ⟨sub9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
