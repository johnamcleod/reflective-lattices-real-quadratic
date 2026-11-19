import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_96 : subd4_1 [3, 0] = true := by decide +kernel
theorem subd4_1_97 : subd4_1 [3, 1] = true := by decide +kernel
theorem subd4_1_98 : subd4_1 [3, 2] = true := by decide +kernel
theorem subd4_1_99 : subd4_1 [3, 3] = true := by decide +kernel
theorem subd4_1_100 : subd4_1 [3, 4] = true := by decide +kernel
theorem subd4_1_101 : subd4_1 [4, -5] = true := by decide +kernel
theorem subd4_1_102 : subd4_1 [4, -4] = true := by decide +kernel
theorem subd4_1_103 : subd4_1 [4, -3] = true := by decide +kernel
theorem subd4_1_104 : subd4_1 [4, -2] = true := by decide +kernel
theorem subd4_1_105 : subd4_1 [4, -1] = true := by decide +kernel
theorem subd4_1_106 : subd4_1 [4, 0] = true := by decide +kernel
theorem subd4_1_107 : subd4_1 [4, 1] = true := by decide +kernel
theorem subd4_1_108 : subd4_1 [4, 2] = true := by decide +kernel
theorem subd4_1_109 : subd4_1 [4, 3] = true := by decide +kernel
theorem subd4_1_110 : subd4_1 [4, 4] = true := by decide +kernel
theorem subd4_1_111 : subd4_1 [5, -4] = true := by decide +kernel
theorem subd4_1_112 : subd4_1 [5, -3] = true := by decide +kernel
theorem subd4_1_113 : subd4_1 [5, -2] = true := by decide +kernel
theorem subd4_1_114 : subd4_1 [5, -1] = true := by decide +kernel
theorem subd4_1_115 : subd4_1 [5, 0] = true := by decide +kernel
theorem subd4_1_116 : subd4_1 [5, 1] = true := by decide +kernel
theorem subd4_1_117 : subd4_1 [5, 2] = true := by decide +kernel
theorem subd4_1_118 : subd4_1 [5, 3] = true := by decide +kernel
theorem subd4_1_119 : subd4_1 [6] = true := by decide +kernel
theorem sbd4_1_3 : ∀ q ∈ blkd4_1_3, subd4_1 q = true := by
  unfold blkd4_1_3
  exact List.forall_mem_cons.2 ⟨subd4_1_96, List.forall_mem_cons.2 ⟨subd4_1_97, List.forall_mem_cons.2 ⟨subd4_1_98, List.forall_mem_cons.2 ⟨subd4_1_99, List.forall_mem_cons.2 ⟨subd4_1_100, List.forall_mem_cons.2 ⟨subd4_1_101, List.forall_mem_cons.2 ⟨subd4_1_102, List.forall_mem_cons.2 ⟨subd4_1_103, List.forall_mem_cons.2 ⟨subd4_1_104, List.forall_mem_cons.2 ⟨subd4_1_105, List.forall_mem_cons.2 ⟨subd4_1_106, List.forall_mem_cons.2 ⟨subd4_1_107, List.forall_mem_cons.2 ⟨subd4_1_108, List.forall_mem_cons.2 ⟨subd4_1_109, List.forall_mem_cons.2 ⟨subd4_1_110, List.forall_mem_cons.2 ⟨subd4_1_111, List.forall_mem_cons.2 ⟨subd4_1_112, List.forall_mem_cons.2 ⟨subd4_1_113, List.forall_mem_cons.2 ⟨subd4_1_114, List.forall_mem_cons.2 ⟨subd4_1_115, List.forall_mem_cons.2 ⟨subd4_1_116, List.forall_mem_cons.2 ⟨subd4_1_117, List.forall_mem_cons.2 ⟨subd4_1_118, List.forall_mem_cons.2 ⟨subd4_1_119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-4, -5] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-4, -4] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-4, -3] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-4, -2] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-4, -1] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-4, 0] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-4, 1] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-4, 2] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-3, -6] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [-3, -5] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [-3, -4] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [-3, -3] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [-3, -2] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [-3, -1] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [-3, 0] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [-3, 1] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [-3, 2] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [-3, 3] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [-2, -6] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [-2, -5] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [-2, -4] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [-2, -3] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [-2, -2] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [-2, -1] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [-2, 0] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [-2, 1] = true := by decide +kernel
theorem subd4_2_26 : subd4_2 [-2, 2] = true := by decide +kernel
theorem subd4_2_27 : subd4_2 [-2, 3] = true := by decide +kernel
theorem subd4_2_28 : subd4_2 [-2, 4] = true := by decide +kernel
theorem subd4_2_29 : subd4_2 [-1, -6] = true := by decide +kernel
theorem subd4_2_30 : subd4_2 [-1, -5] = true := by decide +kernel
theorem subd4_2_31 : subd4_2 [-1, -4] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_cons.2 ⟨subd4_2_26, List.forall_mem_cons.2 ⟨subd4_2_27, List.forall_mem_cons.2 ⟨subd4_2_28, List.forall_mem_cons.2 ⟨subd4_2_29, List.forall_mem_cons.2 ⟨subd4_2_30, List.forall_mem_cons.2 ⟨subd4_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_32 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_33 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_34 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_35 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_36 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_37 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_38 : subd4_2 [-1, 3] = true := by decide +kernel
theorem subd4_2_39 : subd4_2 [-1, 4] = true := by decide +kernel
theorem subd4_2_40 : subd4_2 [-1, 5] = true := by decide +kernel
theorem subd4_2_41 : subd4_2 [0, -6] = true := by decide +kernel
theorem subd4_2_42 : subd4_2 [0, -5] = true := by decide +kernel
theorem subd4_2_43 : subd4_2 [0, -4] = true := by decide +kernel
theorem subd4_2_44 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_45 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_46 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_47 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_48 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_49 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_50 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_51 : subd4_2 [0, 4] = true := by decide +kernel
theorem subd4_2_52 : subd4_2 [0, 5] = true := by decide +kernel
theorem subd4_2_53 : subd4_2 [1, -6] = true := by decide +kernel
theorem subd4_2_54 : subd4_2 [1, -5] = true := by decide +kernel
theorem subd4_2_55 : subd4_2 [1, -4] = true := by decide +kernel
theorem subd4_2_56 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_57 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_58 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_59 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_60 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_61 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_62 : subd4_2 [1, 3] = true := by decide +kernel
theorem subd4_2_63 : subd4_2 [1, 4] = true := by decide +kernel
theorem sbd4_2_1 : ∀ q ∈ blkd4_2_1, subd4_2 q = true := by
  unfold blkd4_2_1
  exact List.forall_mem_cons.2 ⟨subd4_2_32, List.forall_mem_cons.2 ⟨subd4_2_33, List.forall_mem_cons.2 ⟨subd4_2_34, List.forall_mem_cons.2 ⟨subd4_2_35, List.forall_mem_cons.2 ⟨subd4_2_36, List.forall_mem_cons.2 ⟨subd4_2_37, List.forall_mem_cons.2 ⟨subd4_2_38, List.forall_mem_cons.2 ⟨subd4_2_39, List.forall_mem_cons.2 ⟨subd4_2_40, List.forall_mem_cons.2 ⟨subd4_2_41, List.forall_mem_cons.2 ⟨subd4_2_42, List.forall_mem_cons.2 ⟨subd4_2_43, List.forall_mem_cons.2 ⟨subd4_2_44, List.forall_mem_cons.2 ⟨subd4_2_45, List.forall_mem_cons.2 ⟨subd4_2_46, List.forall_mem_cons.2 ⟨subd4_2_47, List.forall_mem_cons.2 ⟨subd4_2_48, List.forall_mem_cons.2 ⟨subd4_2_49, List.forall_mem_cons.2 ⟨subd4_2_50, List.forall_mem_cons.2 ⟨subd4_2_51, List.forall_mem_cons.2 ⟨subd4_2_52, List.forall_mem_cons.2 ⟨subd4_2_53, List.forall_mem_cons.2 ⟨subd4_2_54, List.forall_mem_cons.2 ⟨subd4_2_55, List.forall_mem_cons.2 ⟨subd4_2_56, List.forall_mem_cons.2 ⟨subd4_2_57, List.forall_mem_cons.2 ⟨subd4_2_58, List.forall_mem_cons.2 ⟨subd4_2_59, List.forall_mem_cons.2 ⟨subd4_2_60, List.forall_mem_cons.2 ⟨subd4_2_61, List.forall_mem_cons.2 ⟨subd4_2_62, List.forall_mem_cons.2 ⟨subd4_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
