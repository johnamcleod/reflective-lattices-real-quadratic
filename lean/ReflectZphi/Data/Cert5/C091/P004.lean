import ReflectZphi.Data.Cert5.C091.Base

namespace ReflectZphi.Data.Cert5.C091

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_7_96 : subd6_7 [1, -1] = true := by decide +kernel
theorem subd6_7_97 : subd6_7 [1, 0, -9] = true := by decide +kernel
theorem subd6_7_98 : subd6_7 [1, 0, -8] = true := by decide +kernel
theorem subd6_7_99 : subd6_7 [1, 0, -7] = true := by decide +kernel
theorem subd6_7_100 : subd6_7 [1, 0, -6] = true := by decide +kernel
theorem subd6_7_101 : subd6_7 [1, 0, -5] = true := by decide +kernel
theorem subd6_7_102 : subd6_7 [1, 0, -4] = true := by decide +kernel
theorem subd6_7_103 : subd6_7 [1, 0, -3] = true := by decide +kernel
theorem subd6_7_104 : subd6_7 [1, 0, -2] = true := by decide +kernel
theorem subd6_7_105 : subd6_7 [1, 0, -1] = true := by decide +kernel
theorem subd6_7_106 : subd6_7 [1, 0, 0] = true := by decide +kernel
theorem subd6_7_107 : subd6_7 [1, 0, 1] = true := by decide +kernel
theorem subd6_7_108 : subd6_7 [1, 0, 2] = true := by decide +kernel
theorem subd6_7_109 : subd6_7 [1, 0, 3] = true := by decide +kernel
theorem subd6_7_110 : subd6_7 [1, 0, 4] = true := by decide +kernel
theorem subd6_7_111 : subd6_7 [1, 0, 5] = true := by decide +kernel
theorem subd6_7_112 : subd6_7 [1, 0, 6] = true := by decide +kernel
theorem subd6_7_113 : subd6_7 [1, 0, 7] = true := by decide +kernel
theorem subd6_7_114 : subd6_7 [1, 0, 8] = true := by decide +kernel
theorem subd6_7_115 : subd6_7 [1, 1, -8] = true := by decide +kernel
theorem subd6_7_116 : subd6_7 [1, 1, -7] = true := by decide +kernel
theorem subd6_7_117 : subd6_7 [1, 1, -6] = true := by decide +kernel
theorem subd6_7_118 : subd6_7 [1, 1, -5] = true := by decide +kernel
theorem subd6_7_119 : subd6_7 [1, 1, -4] = true := by decide +kernel
theorem subd6_7_120 : subd6_7 [1, 1, -3] = true := by decide +kernel
theorem subd6_7_121 : subd6_7 [1, 1, -2] = true := by decide +kernel
theorem subd6_7_122 : subd6_7 [1, 1, -1] = true := by decide +kernel
theorem subd6_7_123 : subd6_7 [1, 1, 0] = true := by decide +kernel
theorem subd6_7_124 : subd6_7 [1, 1, 1] = true := by decide +kernel
theorem subd6_7_125 : subd6_7 [1, 1, 2] = true := by decide +kernel
theorem subd6_7_126 : subd6_7 [1, 1, 3] = true := by decide +kernel
theorem subd6_7_127 : subd6_7 [1, 1, 4] = true := by decide +kernel
theorem sbd6_7_3 : ∀ q ∈ blkd6_7_3, subd6_7 q = true := by
  unfold blkd6_7_3
  exact List.forall_mem_cons.2 ⟨subd6_7_96, List.forall_mem_cons.2 ⟨subd6_7_97, List.forall_mem_cons.2 ⟨subd6_7_98, List.forall_mem_cons.2 ⟨subd6_7_99, List.forall_mem_cons.2 ⟨subd6_7_100, List.forall_mem_cons.2 ⟨subd6_7_101, List.forall_mem_cons.2 ⟨subd6_7_102, List.forall_mem_cons.2 ⟨subd6_7_103, List.forall_mem_cons.2 ⟨subd6_7_104, List.forall_mem_cons.2 ⟨subd6_7_105, List.forall_mem_cons.2 ⟨subd6_7_106, List.forall_mem_cons.2 ⟨subd6_7_107, List.forall_mem_cons.2 ⟨subd6_7_108, List.forall_mem_cons.2 ⟨subd6_7_109, List.forall_mem_cons.2 ⟨subd6_7_110, List.forall_mem_cons.2 ⟨subd6_7_111, List.forall_mem_cons.2 ⟨subd6_7_112, List.forall_mem_cons.2 ⟨subd6_7_113, List.forall_mem_cons.2 ⟨subd6_7_114, List.forall_mem_cons.2 ⟨subd6_7_115, List.forall_mem_cons.2 ⟨subd6_7_116, List.forall_mem_cons.2 ⟨subd6_7_117, List.forall_mem_cons.2 ⟨subd6_7_118, List.forall_mem_cons.2 ⟨subd6_7_119, List.forall_mem_cons.2 ⟨subd6_7_120, List.forall_mem_cons.2 ⟨subd6_7_121, List.forall_mem_cons.2 ⟨subd6_7_122, List.forall_mem_cons.2 ⟨subd6_7_123, List.forall_mem_cons.2 ⟨subd6_7_124, List.forall_mem_cons.2 ⟨subd6_7_125, List.forall_mem_cons.2 ⟨subd6_7_126, List.forall_mem_cons.2 ⟨subd6_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_7_128 : subd6_7 [1, 1, 5] = true := by decide +kernel
theorem subd6_7_129 : subd6_7 [1, 1, 6] = true := by decide +kernel
theorem subd6_7_130 : subd6_7 [1, 1, 7] = true := by decide +kernel
theorem sbd6_7_4 : ∀ q ∈ blkd6_7_4, subd6_7 q = true := by
  unfold blkd6_7_4
  exact List.forall_mem_cons.2 ⟨subd6_7_128, List.forall_mem_cons.2 ⟨subd6_7_129, List.forall_mem_cons.2 ⟨subd6_7_130, List.forall_mem_nil _⟩⟩⟩
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem subd7_1_0 : subd7_1 [] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_nil _⟩
theorem subd7_2_0 : subd7_2 [] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_nil _⟩
theorem subd7_3_0 : subd7_3 [] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_nil _⟩
theorem subd7_4_0 : subd7_4 [-2] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-1] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [0] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [1] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [2] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd7_5_0 : subd7_5 [-3] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-1, -4] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-1, -3] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-1, -2] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [-1, -1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [-1, 0] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [-1, 1] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [-1, 2] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [0, -4] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [0, -3] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_14 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_15 : subd7_5 [0, 2] = true := by decide +kernel
theorem subd7_5_16 : subd7_5 [0, 3] = true := by decide +kernel
theorem subd7_5_17 : subd7_5 [1, -3] = true := by decide +kernel
theorem subd7_5_18 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_19 : subd7_5 [1, -1] = true := by decide +kernel
theorem subd7_5_20 : subd7_5 [1, 0] = true := by decide +kernel
theorem subd7_5_21 : subd7_5 [1, 1] = true := by decide +kernel
theorem subd7_5_22 : subd7_5 [1, 2] = true := by decide +kernel
theorem subd7_5_23 : subd7_5 [1, 3] = true := by decide +kernel
theorem subd7_5_24 : subd7_5 [2] = true := by decide +kernel
theorem subd7_5_25 : subd7_5 [3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_cons.2 ⟨subd7_5_14, List.forall_mem_cons.2 ⟨subd7_5_15, List.forall_mem_cons.2 ⟨subd7_5_16, List.forall_mem_cons.2 ⟨subd7_5_17, List.forall_mem_cons.2 ⟨subd7_5_18, List.forall_mem_cons.2 ⟨subd7_5_19, List.forall_mem_cons.2 ⟨subd7_5_20, List.forall_mem_cons.2 ⟨subd7_5_21, List.forall_mem_cons.2 ⟨subd7_5_22, List.forall_mem_cons.2 ⟨subd7_5_23, List.forall_mem_cons.2 ⟨subd7_5_24, List.forall_mem_cons.2 ⟨subd7_5_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_0 : subd7_6 [-2] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [1, 2] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_0 : subd7_7 [-2] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-1, -3] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [-1, -2] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [-1, -1, -8] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [-1, -1, -7] = true := by decide +kernel
theorem subd7_7_5 : subd7_7 [-1, -1, -6] = true := by decide +kernel
theorem subd7_7_6 : subd7_7 [-1, -1, -5] = true := by decide +kernel
theorem subd7_7_7 : subd7_7 [-1, -1, -4] = true := by decide +kernel
theorem subd7_7_8 : subd7_7 [-1, -1, -3] = true := by decide +kernel
theorem subd7_7_9 : subd7_7 [-1, -1, -2] = true := by decide +kernel
theorem subd7_7_10 : subd7_7 [-1, -1, -1] = true := by decide +kernel
theorem subd7_7_11 : subd7_7 [-1, -1, 0] = true := by decide +kernel
theorem subd7_7_12 : subd7_7 [-1, -1, 1] = true := by decide +kernel
theorem subd7_7_13 : subd7_7 [-1, -1, 2] = true := by decide +kernel
theorem subd7_7_14 : subd7_7 [-1, -1, 3] = true := by decide +kernel
theorem subd7_7_15 : subd7_7 [-1, -1, 4] = true := by decide +kernel
theorem subd7_7_16 : subd7_7 [-1, -1, 5] = true := by decide +kernel
theorem subd7_7_17 : subd7_7 [-1, -1, 6] = true := by decide +kernel
theorem subd7_7_18 : subd7_7 [-1, -1, 7] = true := by decide +kernel
theorem subd7_7_19 : subd7_7 [-1, 0, -9] = true := by decide +kernel
theorem subd7_7_20 : subd7_7 [-1, 0, -8] = true := by decide +kernel
theorem subd7_7_21 : subd7_7 [-1, 0, -7] = true := by decide +kernel
theorem subd7_7_22 : subd7_7 [-1, 0, -6] = true := by decide +kernel
theorem subd7_7_23 : subd7_7 [-1, 0, -5] = true := by decide +kernel
theorem subd7_7_24 : subd7_7 [-1, 0, -4] = true := by decide +kernel
theorem subd7_7_25 : subd7_7 [-1, 0, -3] = true := by decide +kernel
theorem subd7_7_26 : subd7_7 [-1, 0, -2] = true := by decide +kernel
theorem subd7_7_27 : subd7_7 [-1, 0, -1] = true := by decide +kernel
theorem subd7_7_28 : subd7_7 [-1, 0, 0] = true := by decide +kernel
theorem subd7_7_29 : subd7_7 [-1, 0, 1] = true := by decide +kernel
theorem subd7_7_30 : subd7_7 [-1, 0, 2] = true := by decide +kernel
theorem subd7_7_31 : subd7_7 [-1, 0, 3] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_cons.2 ⟨subd7_7_5, List.forall_mem_cons.2 ⟨subd7_7_6, List.forall_mem_cons.2 ⟨subd7_7_7, List.forall_mem_cons.2 ⟨subd7_7_8, List.forall_mem_cons.2 ⟨subd7_7_9, List.forall_mem_cons.2 ⟨subd7_7_10, List.forall_mem_cons.2 ⟨subd7_7_11, List.forall_mem_cons.2 ⟨subd7_7_12, List.forall_mem_cons.2 ⟨subd7_7_13, List.forall_mem_cons.2 ⟨subd7_7_14, List.forall_mem_cons.2 ⟨subd7_7_15, List.forall_mem_cons.2 ⟨subd7_7_16, List.forall_mem_cons.2 ⟨subd7_7_17, List.forall_mem_cons.2 ⟨subd7_7_18, List.forall_mem_cons.2 ⟨subd7_7_19, List.forall_mem_cons.2 ⟨subd7_7_20, List.forall_mem_cons.2 ⟨subd7_7_21, List.forall_mem_cons.2 ⟨subd7_7_22, List.forall_mem_cons.2 ⟨subd7_7_23, List.forall_mem_cons.2 ⟨subd7_7_24, List.forall_mem_cons.2 ⟨subd7_7_25, List.forall_mem_cons.2 ⟨subd7_7_26, List.forall_mem_cons.2 ⟨subd7_7_27, List.forall_mem_cons.2 ⟨subd7_7_28, List.forall_mem_cons.2 ⟨subd7_7_29, List.forall_mem_cons.2 ⟨subd7_7_30, List.forall_mem_cons.2 ⟨subd7_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_32 : subd7_7 [-1, 0, 4] = true := by decide +kernel
theorem subd7_7_33 : subd7_7 [-1, 0, 5] = true := by decide +kernel
theorem subd7_7_34 : subd7_7 [-1, 0, 6] = true := by decide +kernel
theorem subd7_7_35 : subd7_7 [-1, 0, 7] = true := by decide +kernel
theorem subd7_7_36 : subd7_7 [-1, 0, 8] = true := by decide +kernel
theorem subd7_7_37 : subd7_7 [-1, 1, -8] = true := by decide +kernel
theorem subd7_7_38 : subd7_7 [-1, 1, -7] = true := by decide +kernel
theorem subd7_7_39 : subd7_7 [-1, 1, -6] = true := by decide +kernel
theorem subd7_7_40 : subd7_7 [-1, 1, -5] = true := by decide +kernel
theorem subd7_7_41 : subd7_7 [-1, 1, -4] = true := by decide +kernel
theorem subd7_7_42 : subd7_7 [-1, 1, -3] = true := by decide +kernel
theorem subd7_7_43 : subd7_7 [-1, 1, -2] = true := by decide +kernel
theorem subd7_7_44 : subd7_7 [-1, 1, -1] = true := by decide +kernel
theorem subd7_7_45 : subd7_7 [-1, 1, 0] = true := by decide +kernel
theorem subd7_7_46 : subd7_7 [-1, 1, 1] = true := by decide +kernel
theorem subd7_7_47 : subd7_7 [-1, 1, 2] = true := by decide +kernel
theorem subd7_7_48 : subd7_7 [-1, 1, 3] = true := by decide +kernel
theorem subd7_7_49 : subd7_7 [-1, 1, 4] = true := by decide +kernel
theorem subd7_7_50 : subd7_7 [-1, 1, 5] = true := by decide +kernel
theorem subd7_7_51 : subd7_7 [-1, 1, 6] = true := by decide +kernel
theorem subd7_7_52 : subd7_7 [-1, 1, 7] = true := by decide +kernel
theorem subd7_7_53 : subd7_7 [-1, 2] = true := by decide +kernel
theorem subd7_7_54 : subd7_7 [0, -3] = true := by decide +kernel
theorem subd7_7_55 : subd7_7 [0, -2] = true := by decide +kernel
theorem subd7_7_56 : subd7_7 [0, -1, -9] = true := by decide +kernel
theorem subd7_7_57 : subd7_7 [0, -1, -8] = true := by decide +kernel
theorem subd7_7_58 : subd7_7 [0, -1, -7] = true := by decide +kernel
theorem subd7_7_59 : subd7_7 [0, -1, -6] = true := by decide +kernel
theorem subd7_7_60 : subd7_7 [0, -1, -5] = true := by decide +kernel
theorem subd7_7_61 : subd7_7 [0, -1, -4] = true := by decide +kernel
theorem subd7_7_62 : subd7_7 [0, -1, -3] = true := by decide +kernel
theorem subd7_7_63 : subd7_7 [0, -1, -2] = true := by decide +kernel
theorem sbd7_7_1 : ∀ q ∈ blkd7_7_1, subd7_7 q = true := by
  unfold blkd7_7_1
  exact List.forall_mem_cons.2 ⟨subd7_7_32, List.forall_mem_cons.2 ⟨subd7_7_33, List.forall_mem_cons.2 ⟨subd7_7_34, List.forall_mem_cons.2 ⟨subd7_7_35, List.forall_mem_cons.2 ⟨subd7_7_36, List.forall_mem_cons.2 ⟨subd7_7_37, List.forall_mem_cons.2 ⟨subd7_7_38, List.forall_mem_cons.2 ⟨subd7_7_39, List.forall_mem_cons.2 ⟨subd7_7_40, List.forall_mem_cons.2 ⟨subd7_7_41, List.forall_mem_cons.2 ⟨subd7_7_42, List.forall_mem_cons.2 ⟨subd7_7_43, List.forall_mem_cons.2 ⟨subd7_7_44, List.forall_mem_cons.2 ⟨subd7_7_45, List.forall_mem_cons.2 ⟨subd7_7_46, List.forall_mem_cons.2 ⟨subd7_7_47, List.forall_mem_cons.2 ⟨subd7_7_48, List.forall_mem_cons.2 ⟨subd7_7_49, List.forall_mem_cons.2 ⟨subd7_7_50, List.forall_mem_cons.2 ⟨subd7_7_51, List.forall_mem_cons.2 ⟨subd7_7_52, List.forall_mem_cons.2 ⟨subd7_7_53, List.forall_mem_cons.2 ⟨subd7_7_54, List.forall_mem_cons.2 ⟨subd7_7_55, List.forall_mem_cons.2 ⟨subd7_7_56, List.forall_mem_cons.2 ⟨subd7_7_57, List.forall_mem_cons.2 ⟨subd7_7_58, List.forall_mem_cons.2 ⟨subd7_7_59, List.forall_mem_cons.2 ⟨subd7_7_60, List.forall_mem_cons.2 ⟨subd7_7_61, List.forall_mem_cons.2 ⟨subd7_7_62, List.forall_mem_cons.2 ⟨subd7_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_64 : subd7_7 [0, -1, -1] = true := by decide +kernel
theorem subd7_7_65 : subd7_7 [0, -1, 0] = true := by decide +kernel
theorem subd7_7_66 : subd7_7 [0, -1, 1] = true := by decide +kernel
theorem subd7_7_67 : subd7_7 [0, -1, 2] = true := by decide +kernel
theorem subd7_7_68 : subd7_7 [0, -1, 3] = true := by decide +kernel
theorem subd7_7_69 : subd7_7 [0, -1, 4] = true := by decide +kernel
theorem subd7_7_70 : subd7_7 [0, -1, 5] = true := by decide +kernel
theorem subd7_7_71 : subd7_7 [0, -1, 6] = true := by decide +kernel
theorem subd7_7_72 : subd7_7 [0, -1, 7] = true := by decide +kernel
theorem subd7_7_73 : subd7_7 [0, -1, 8] = true := by decide +kernel
theorem subd7_7_74 : subd7_7 [0, 0, -10] = true := by decide +kernel
theorem subd7_7_75 : subd7_7 [0, 0, -9] = true := by decide +kernel
theorem subd7_7_76 : subd7_7 [0, 0, -8] = true := by decide +kernel
theorem subd7_7_77 : subd7_7 [0, 0, -7] = true := by decide +kernel
theorem subd7_7_78 : subd7_7 [0, 0, -6] = true := by decide +kernel
theorem subd7_7_79 : subd7_7 [0, 0, -5] = true := by decide +kernel
theorem subd7_7_80 : subd7_7 [0, 0, -4] = true := by decide +kernel
theorem subd7_7_81 : subd7_7 [0, 0, -3] = true := by decide +kernel
theorem subd7_7_82 : subd7_7 [0, 0, -2] = true := by decide +kernel
theorem subd7_7_83 : subd7_7 [0, 0, -1] = true := by decide +kernel
theorem subd7_7_84 : subd7_7 [0, 0, 0] = true := by decide +kernel
theorem subd7_7_85 : subd7_7 [0, 0, 1] = true := by decide +kernel
theorem subd7_7_86 : subd7_7 [0, 0, 2] = true := by decide +kernel
theorem subd7_7_87 : subd7_7 [0, 0, 3] = true := by decide +kernel
theorem subd7_7_88 : subd7_7 [0, 0, 4] = true := by decide +kernel
theorem subd7_7_89 : subd7_7 [0, 0, 5] = true := by decide +kernel
theorem subd7_7_90 : subd7_7 [0, 0, 6] = true := by decide +kernel
theorem subd7_7_91 : subd7_7 [0, 0, 7] = true := by decide +kernel
theorem subd7_7_92 : subd7_7 [0, 0, 8] = true := by decide +kernel
theorem subd7_7_93 : subd7_7 [0, 0, 9] = true := by decide +kernel
theorem subd7_7_94 : subd7_7 [0, 1, -9] = true := by decide +kernel
theorem subd7_7_95 : subd7_7 [0, 1, -8] = true := by decide +kernel
theorem sbd7_7_2 : ∀ q ∈ blkd7_7_2, subd7_7 q = true := by
  unfold blkd7_7_2
  exact List.forall_mem_cons.2 ⟨subd7_7_64, List.forall_mem_cons.2 ⟨subd7_7_65, List.forall_mem_cons.2 ⟨subd7_7_66, List.forall_mem_cons.2 ⟨subd7_7_67, List.forall_mem_cons.2 ⟨subd7_7_68, List.forall_mem_cons.2 ⟨subd7_7_69, List.forall_mem_cons.2 ⟨subd7_7_70, List.forall_mem_cons.2 ⟨subd7_7_71, List.forall_mem_cons.2 ⟨subd7_7_72, List.forall_mem_cons.2 ⟨subd7_7_73, List.forall_mem_cons.2 ⟨subd7_7_74, List.forall_mem_cons.2 ⟨subd7_7_75, List.forall_mem_cons.2 ⟨subd7_7_76, List.forall_mem_cons.2 ⟨subd7_7_77, List.forall_mem_cons.2 ⟨subd7_7_78, List.forall_mem_cons.2 ⟨subd7_7_79, List.forall_mem_cons.2 ⟨subd7_7_80, List.forall_mem_cons.2 ⟨subd7_7_81, List.forall_mem_cons.2 ⟨subd7_7_82, List.forall_mem_cons.2 ⟨subd7_7_83, List.forall_mem_cons.2 ⟨subd7_7_84, List.forall_mem_cons.2 ⟨subd7_7_85, List.forall_mem_cons.2 ⟨subd7_7_86, List.forall_mem_cons.2 ⟨subd7_7_87, List.forall_mem_cons.2 ⟨subd7_7_88, List.forall_mem_cons.2 ⟨subd7_7_89, List.forall_mem_cons.2 ⟨subd7_7_90, List.forall_mem_cons.2 ⟨subd7_7_91, List.forall_mem_cons.2 ⟨subd7_7_92, List.forall_mem_cons.2 ⟨subd7_7_93, List.forall_mem_cons.2 ⟨subd7_7_94, List.forall_mem_cons.2 ⟨subd7_7_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_96 : subd7_7 [0, 1, -7] = true := by decide +kernel
theorem subd7_7_97 : subd7_7 [0, 1, -6] = true := by decide +kernel
theorem subd7_7_98 : subd7_7 [0, 1, -5] = true := by decide +kernel
theorem subd7_7_99 : subd7_7 [0, 1, -4] = true := by decide +kernel
theorem subd7_7_100 : subd7_7 [0, 1, -3] = true := by decide +kernel
theorem subd7_7_101 : subd7_7 [0, 1, -2] = true := by decide +kernel
theorem subd7_7_102 : subd7_7 [0, 1, -1] = true := by decide +kernel
theorem subd7_7_103 : subd7_7 [0, 1, 0] = true := by decide +kernel
theorem subd7_7_104 : subd7_7 [0, 1, 1] = true := by decide +kernel
theorem subd7_7_105 : subd7_7 [0, 1, 2] = true := by decide +kernel
theorem subd7_7_106 : subd7_7 [0, 1, 3] = true := by decide +kernel
theorem subd7_7_107 : subd7_7 [0, 1, 4] = true := by decide +kernel
theorem subd7_7_108 : subd7_7 [0, 1, 5] = true := by decide +kernel
theorem subd7_7_109 : subd7_7 [0, 1, 6] = true := by decide +kernel
theorem subd7_7_110 : subd7_7 [0, 1, 7] = true := by decide +kernel
theorem subd7_7_111 : subd7_7 [0, 1, 8] = true := by decide +kernel
theorem subd7_7_112 : subd7_7 [0, 2] = true := by decide +kernel
theorem subd7_7_113 : subd7_7 [1, -3] = true := by decide +kernel
theorem subd7_7_114 : subd7_7 [1, -2] = true := by decide +kernel
theorem subd7_7_115 : subd7_7 [1, -1, -8] = true := by decide +kernel
theorem subd7_7_116 : subd7_7 [1, -1, -7] = true := by decide +kernel
theorem subd7_7_117 : subd7_7 [1, -1, -6] = true := by decide +kernel
theorem subd7_7_118 : subd7_7 [1, -1, -5] = true := by decide +kernel
theorem subd7_7_119 : subd7_7 [1, -1, -4] = true := by decide +kernel
theorem subd7_7_120 : subd7_7 [1, -1, -3] = true := by decide +kernel
theorem subd7_7_121 : subd7_7 [1, -1, -2] = true := by decide +kernel
theorem subd7_7_122 : subd7_7 [1, -1, -1] = true := by decide +kernel
theorem subd7_7_123 : subd7_7 [1, -1, 0] = true := by decide +kernel
theorem subd7_7_124 : subd7_7 [1, -1, 1] = true := by decide +kernel
theorem subd7_7_125 : subd7_7 [1, -1, 2] = true := by decide +kernel
theorem subd7_7_126 : subd7_7 [1, -1, 3] = true := by decide +kernel
theorem subd7_7_127 : subd7_7 [1, -1, 4] = true := by decide +kernel
theorem sbd7_7_3 : ∀ q ∈ blkd7_7_3, subd7_7 q = true := by
  unfold blkd7_7_3
  exact List.forall_mem_cons.2 ⟨subd7_7_96, List.forall_mem_cons.2 ⟨subd7_7_97, List.forall_mem_cons.2 ⟨subd7_7_98, List.forall_mem_cons.2 ⟨subd7_7_99, List.forall_mem_cons.2 ⟨subd7_7_100, List.forall_mem_cons.2 ⟨subd7_7_101, List.forall_mem_cons.2 ⟨subd7_7_102, List.forall_mem_cons.2 ⟨subd7_7_103, List.forall_mem_cons.2 ⟨subd7_7_104, List.forall_mem_cons.2 ⟨subd7_7_105, List.forall_mem_cons.2 ⟨subd7_7_106, List.forall_mem_cons.2 ⟨subd7_7_107, List.forall_mem_cons.2 ⟨subd7_7_108, List.forall_mem_cons.2 ⟨subd7_7_109, List.forall_mem_cons.2 ⟨subd7_7_110, List.forall_mem_cons.2 ⟨subd7_7_111, List.forall_mem_cons.2 ⟨subd7_7_112, List.forall_mem_cons.2 ⟨subd7_7_113, List.forall_mem_cons.2 ⟨subd7_7_114, List.forall_mem_cons.2 ⟨subd7_7_115, List.forall_mem_cons.2 ⟨subd7_7_116, List.forall_mem_cons.2 ⟨subd7_7_117, List.forall_mem_cons.2 ⟨subd7_7_118, List.forall_mem_cons.2 ⟨subd7_7_119, List.forall_mem_cons.2 ⟨subd7_7_120, List.forall_mem_cons.2 ⟨subd7_7_121, List.forall_mem_cons.2 ⟨subd7_7_122, List.forall_mem_cons.2 ⟨subd7_7_123, List.forall_mem_cons.2 ⟨subd7_7_124, List.forall_mem_cons.2 ⟨subd7_7_125, List.forall_mem_cons.2 ⟨subd7_7_126, List.forall_mem_cons.2 ⟨subd7_7_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_128 : subd7_7 [1, -1, 5] = true := by decide +kernel
theorem subd7_7_129 : subd7_7 [1, -1, 6] = true := by decide +kernel
theorem subd7_7_130 : subd7_7 [1, -1, 7] = true := by decide +kernel
theorem subd7_7_131 : subd7_7 [1, 0, -9] = true := by decide +kernel
theorem subd7_7_132 : subd7_7 [1, 0, -8] = true := by decide +kernel
theorem subd7_7_133 : subd7_7 [1, 0, -7] = true := by decide +kernel
theorem subd7_7_134 : subd7_7 [1, 0, -6] = true := by decide +kernel
theorem subd7_7_135 : subd7_7 [1, 0, -5] = true := by decide +kernel
theorem subd7_7_136 : subd7_7 [1, 0, -4] = true := by decide +kernel
theorem subd7_7_137 : subd7_7 [1, 0, -3] = true := by decide +kernel
theorem subd7_7_138 : subd7_7 [1, 0, -2] = true := by decide +kernel
theorem subd7_7_139 : subd7_7 [1, 0, -1] = true := by decide +kernel
theorem subd7_7_140 : subd7_7 [1, 0, 0] = true := by decide +kernel
theorem subd7_7_141 : subd7_7 [1, 0, 1] = true := by decide +kernel
theorem subd7_7_142 : subd7_7 [1, 0, 2] = true := by decide +kernel
theorem subd7_7_143 : subd7_7 [1, 0, 3] = true := by decide +kernel
theorem subd7_7_144 : subd7_7 [1, 0, 4] = true := by decide +kernel
theorem subd7_7_145 : subd7_7 [1, 0, 5] = true := by decide +kernel
theorem subd7_7_146 : subd7_7 [1, 0, 6] = true := by decide +kernel
theorem subd7_7_147 : subd7_7 [1, 0, 7] = true := by decide +kernel
theorem subd7_7_148 : subd7_7 [1, 0, 8] = true := by decide +kernel
theorem subd7_7_149 : subd7_7 [1, 1, -8] = true := by decide +kernel
theorem subd7_7_150 : subd7_7 [1, 1, -7] = true := by decide +kernel
theorem subd7_7_151 : subd7_7 [1, 1, -6] = true := by decide +kernel
theorem subd7_7_152 : subd7_7 [1, 1, -5] = true := by decide +kernel
theorem subd7_7_153 : subd7_7 [1, 1, -4] = true := by decide +kernel
theorem subd7_7_154 : subd7_7 [1, 1, -3] = true := by decide +kernel
theorem subd7_7_155 : subd7_7 [1, 1, -2] = true := by decide +kernel
theorem subd7_7_156 : subd7_7 [1, 1, -1] = true := by decide +kernel
theorem subd7_7_157 : subd7_7 [1, 1, 0] = true := by decide +kernel
theorem subd7_7_158 : subd7_7 [1, 1, 1] = true := by decide +kernel
theorem subd7_7_159 : subd7_7 [1, 1, 2] = true := by decide +kernel
theorem sbd7_7_4 : ∀ q ∈ blkd7_7_4, subd7_7 q = true := by
  unfold blkd7_7_4
  exact List.forall_mem_cons.2 ⟨subd7_7_128, List.forall_mem_cons.2 ⟨subd7_7_129, List.forall_mem_cons.2 ⟨subd7_7_130, List.forall_mem_cons.2 ⟨subd7_7_131, List.forall_mem_cons.2 ⟨subd7_7_132, List.forall_mem_cons.2 ⟨subd7_7_133, List.forall_mem_cons.2 ⟨subd7_7_134, List.forall_mem_cons.2 ⟨subd7_7_135, List.forall_mem_cons.2 ⟨subd7_7_136, List.forall_mem_cons.2 ⟨subd7_7_137, List.forall_mem_cons.2 ⟨subd7_7_138, List.forall_mem_cons.2 ⟨subd7_7_139, List.forall_mem_cons.2 ⟨subd7_7_140, List.forall_mem_cons.2 ⟨subd7_7_141, List.forall_mem_cons.2 ⟨subd7_7_142, List.forall_mem_cons.2 ⟨subd7_7_143, List.forall_mem_cons.2 ⟨subd7_7_144, List.forall_mem_cons.2 ⟨subd7_7_145, List.forall_mem_cons.2 ⟨subd7_7_146, List.forall_mem_cons.2 ⟨subd7_7_147, List.forall_mem_cons.2 ⟨subd7_7_148, List.forall_mem_cons.2 ⟨subd7_7_149, List.forall_mem_cons.2 ⟨subd7_7_150, List.forall_mem_cons.2 ⟨subd7_7_151, List.forall_mem_cons.2 ⟨subd7_7_152, List.forall_mem_cons.2 ⟨subd7_7_153, List.forall_mem_cons.2 ⟨subd7_7_154, List.forall_mem_cons.2 ⟨subd7_7_155, List.forall_mem_cons.2 ⟨subd7_7_156, List.forall_mem_cons.2 ⟨subd7_7_157, List.forall_mem_cons.2 ⟨subd7_7_158, List.forall_mem_cons.2 ⟨subd7_7_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_160 : subd7_7 [1, 1, 3] = true := by decide +kernel
theorem subd7_7_161 : subd7_7 [1, 1, 4] = true := by decide +kernel
theorem subd7_7_162 : subd7_7 [1, 1, 5] = true := by decide +kernel
theorem subd7_7_163 : subd7_7 [1, 1, 6] = true := by decide +kernel
theorem subd7_7_164 : subd7_7 [1, 1, 7] = true := by decide +kernel
theorem subd7_7_165 : subd7_7 [1, 2] = true := by decide +kernel
theorem subd7_7_166 : subd7_7 [2] = true := by decide +kernel
theorem sbd7_7_5 : ∀ q ∈ blkd7_7_5, subd7_7 q = true := by
  unfold blkd7_7_5
  exact List.forall_mem_cons.2 ⟨subd7_7_160, List.forall_mem_cons.2 ⟨subd7_7_161, List.forall_mem_cons.2 ⟨subd7_7_162, List.forall_mem_cons.2 ⟨subd7_7_163, List.forall_mem_cons.2 ⟨subd7_7_164, List.forall_mem_cons.2 ⟨subd7_7_165, List.forall_mem_cons.2 ⟨subd7_7_166, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_0 : subd8_0 [] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_nil _⟩
theorem subd8_1_0 : subd8_1 [] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_nil _⟩
theorem subd8_2_0 : subd8_2 [] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_nil _⟩
theorem subd8_3_0 : subd8_3 [] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_nil _⟩
theorem subd8_4_0 : subd8_4 [] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_nil _⟩
theorem subd8_5_0 : subd8_5 [-2] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [0, -2] = true := by decide +kernel
theorem subd8_5_3 : subd8_5 [0, -1] = true := by decide +kernel
theorem subd8_5_4 : subd8_5 [0, 0] = true := by decide +kernel
theorem subd8_5_5 : subd8_5 [0, 1] = true := by decide +kernel
theorem subd8_5_6 : subd8_5 [1] = true := by decide +kernel
theorem subd8_5_7 : subd8_5 [2] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_cons.2 ⟨subd8_5_3, List.forall_mem_cons.2 ⟨subd8_5_4, List.forall_mem_cons.2 ⟨subd8_5_5, List.forall_mem_cons.2 ⟨subd8_5_6, List.forall_mem_cons.2 ⟨subd8_5_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_0 : subd8_6 [-1] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [0, 0] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [1] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd8_7_0 : subd8_7 [-2] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-1, -3] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [-1, -2] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [-1, -1] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [-1, 0] = true := by decide +kernel
theorem subd8_7_5 : subd8_7 [-1, 1] = true := by decide +kernel
theorem subd8_7_6 : subd8_7 [-1, 2] = true := by decide +kernel
theorem subd8_7_7 : subd8_7 [0, -3] = true := by decide +kernel
theorem subd8_7_8 : subd8_7 [0, -2] = true := by decide +kernel
theorem subd8_7_9 : subd8_7 [0, -1] = true := by decide +kernel
theorem subd8_7_10 : subd8_7 [0, 0, -7] = true := by decide +kernel
theorem subd8_7_11 : subd8_7 [0, 0, -6] = true := by decide +kernel
theorem subd8_7_12 : subd8_7 [0, 0, -5] = true := by decide +kernel
theorem subd8_7_13 : subd8_7 [0, 0, -4] = true := by decide +kernel
theorem subd8_7_14 : subd8_7 [0, 0, -3] = true := by decide +kernel
theorem subd8_7_15 : subd8_7 [0, 0, -2] = true := by decide +kernel
theorem subd8_7_16 : subd8_7 [0, 0, -1] = true := by decide +kernel
theorem subd8_7_17 : subd8_7 [0, 0, 0] = true := by decide +kernel
theorem subd8_7_18 : subd8_7 [0, 0, 1] = true := by decide +kernel
theorem subd8_7_19 : subd8_7 [0, 0, 2] = true := by decide +kernel
theorem subd8_7_20 : subd8_7 [0, 0, 3] = true := by decide +kernel
theorem subd8_7_21 : subd8_7 [0, 0, 4] = true := by decide +kernel
theorem subd8_7_22 : subd8_7 [0, 0, 5] = true := by decide +kernel
theorem subd8_7_23 : subd8_7 [0, 0, 6] = true := by decide +kernel
theorem subd8_7_24 : subd8_7 [0, 1] = true := by decide +kernel
theorem subd8_7_25 : subd8_7 [0, 2] = true := by decide +kernel
theorem subd8_7_26 : subd8_7 [1, -3] = true := by decide +kernel
theorem subd8_7_27 : subd8_7 [1, -2] = true := by decide +kernel
theorem subd8_7_28 : subd8_7 [1, -1] = true := by decide +kernel
theorem subd8_7_29 : subd8_7 [1, 0] = true := by decide +kernel
theorem subd8_7_30 : subd8_7 [1, 1] = true := by decide +kernel
theorem subd8_7_31 : subd8_7 [1, 2] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_cons.2 ⟨subd8_7_5, List.forall_mem_cons.2 ⟨subd8_7_6, List.forall_mem_cons.2 ⟨subd8_7_7, List.forall_mem_cons.2 ⟨subd8_7_8, List.forall_mem_cons.2 ⟨subd8_7_9, List.forall_mem_cons.2 ⟨subd8_7_10, List.forall_mem_cons.2 ⟨subd8_7_11, List.forall_mem_cons.2 ⟨subd8_7_12, List.forall_mem_cons.2 ⟨subd8_7_13, List.forall_mem_cons.2 ⟨subd8_7_14, List.forall_mem_cons.2 ⟨subd8_7_15, List.forall_mem_cons.2 ⟨subd8_7_16, List.forall_mem_cons.2 ⟨subd8_7_17, List.forall_mem_cons.2 ⟨subd8_7_18, List.forall_mem_cons.2 ⟨subd8_7_19, List.forall_mem_cons.2 ⟨subd8_7_20, List.forall_mem_cons.2 ⟨subd8_7_21, List.forall_mem_cons.2 ⟨subd8_7_22, List.forall_mem_cons.2 ⟨subd8_7_23, List.forall_mem_cons.2 ⟨subd8_7_24, List.forall_mem_cons.2 ⟨subd8_7_25, List.forall_mem_cons.2 ⟨subd8_7_26, List.forall_mem_cons.2 ⟨subd8_7_27, List.forall_mem_cons.2 ⟨subd8_7_28, List.forall_mem_cons.2 ⟨subd8_7_29, List.forall_mem_cons.2 ⟨subd8_7_30, List.forall_mem_cons.2 ⟨subd8_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_32 : subd8_7 [2] = true := by decide +kernel
theorem sbd8_7_1 : ∀ q ∈ blkd8_7_1, subd8_7 q = true := by
  unfold blkd8_7_1
  exact List.forall_mem_cons.2 ⟨subd8_7_32, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C091
