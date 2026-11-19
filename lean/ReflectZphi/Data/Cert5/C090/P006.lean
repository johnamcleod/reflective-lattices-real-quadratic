import ReflectZphi.Data.Cert5.C090.Base

namespace ReflectZphi.Data.Cert5.C090

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_5_96 : subd4_5 [0, 1, 5] = true := by decide +kernel
theorem subd4_5_97 : subd4_5 [0, 1, 6] = true := by decide +kernel
theorem subd4_5_98 : subd4_5 [0, 1, 7] = true := by decide +kernel
theorem subd4_5_99 : subd4_5 [0, 1, 8] = true := by decide +kernel
theorem subd4_5_100 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_101 : subd4_5 [1, -1] = true := by decide +kernel
theorem subd4_5_102 : subd4_5 [1, 0, -9] = true := by decide +kernel
theorem subd4_5_103 : subd4_5 [1, 0, -8] = true := by decide +kernel
theorem subd4_5_104 : subd4_5 [1, 0, -7] = true := by decide +kernel
theorem subd4_5_105 : subd4_5 [1, 0, -6] = true := by decide +kernel
theorem subd4_5_106 : subd4_5 [1, 0, -5] = true := by decide +kernel
theorem subd4_5_107 : subd4_5 [1, 0, -4] = true := by decide +kernel
theorem subd4_5_108 : subd4_5 [1, 0, -3] = true := by decide +kernel
theorem subd4_5_109 : subd4_5 [1, 0, -2] = true := by decide +kernel
theorem subd4_5_110 : subd4_5 [1, 0, -1] = true := by decide +kernel
theorem subd4_5_111 : subd4_5 [1, 0, 0] = true := by decide +kernel
theorem subd4_5_112 : subd4_5 [1, 0, 1] = true := by decide +kernel
theorem subd4_5_113 : subd4_5 [1, 0, 2] = true := by decide +kernel
theorem subd4_5_114 : subd4_5 [1, 0, 3] = true := by decide +kernel
theorem subd4_5_115 : subd4_5 [1, 0, 4] = true := by decide +kernel
theorem subd4_5_116 : subd4_5 [1, 0, 5] = true := by decide +kernel
theorem subd4_5_117 : subd4_5 [1, 0, 6] = true := by decide +kernel
theorem subd4_5_118 : subd4_5 [1, 0, 7] = true := by decide +kernel
theorem subd4_5_119 : subd4_5 [1, 0, 8] = true := by decide +kernel
theorem subd4_5_120 : subd4_5 [1, 0, 9] = true := by decide +kernel
theorem subd4_5_121 : subd4_5 [1, 1, -8] = true := by decide +kernel
theorem subd4_5_122 : subd4_5 [1, 1, -7] = true := by decide +kernel
theorem subd4_5_123 : subd4_5 [1, 1, -6] = true := by decide +kernel
theorem subd4_5_124 : subd4_5 [1, 1, -5] = true := by decide +kernel
theorem subd4_5_125 : subd4_5 [1, 1, -4] = true := by decide +kernel
theorem subd4_5_126 : subd4_5 [1, 1, -3] = true := by decide +kernel
theorem subd4_5_127 : subd4_5 [1, 1, -2] = true := by decide +kernel
theorem sbd4_5_3 : ∀ q ∈ blkd4_5_3, subd4_5 q = true := by
  unfold blkd4_5_3
  exact List.forall_mem_cons.2 ⟨subd4_5_96, List.forall_mem_cons.2 ⟨subd4_5_97, List.forall_mem_cons.2 ⟨subd4_5_98, List.forall_mem_cons.2 ⟨subd4_5_99, List.forall_mem_cons.2 ⟨subd4_5_100, List.forall_mem_cons.2 ⟨subd4_5_101, List.forall_mem_cons.2 ⟨subd4_5_102, List.forall_mem_cons.2 ⟨subd4_5_103, List.forall_mem_cons.2 ⟨subd4_5_104, List.forall_mem_cons.2 ⟨subd4_5_105, List.forall_mem_cons.2 ⟨subd4_5_106, List.forall_mem_cons.2 ⟨subd4_5_107, List.forall_mem_cons.2 ⟨subd4_5_108, List.forall_mem_cons.2 ⟨subd4_5_109, List.forall_mem_cons.2 ⟨subd4_5_110, List.forall_mem_cons.2 ⟨subd4_5_111, List.forall_mem_cons.2 ⟨subd4_5_112, List.forall_mem_cons.2 ⟨subd4_5_113, List.forall_mem_cons.2 ⟨subd4_5_114, List.forall_mem_cons.2 ⟨subd4_5_115, List.forall_mem_cons.2 ⟨subd4_5_116, List.forall_mem_cons.2 ⟨subd4_5_117, List.forall_mem_cons.2 ⟨subd4_5_118, List.forall_mem_cons.2 ⟨subd4_5_119, List.forall_mem_cons.2 ⟨subd4_5_120, List.forall_mem_cons.2 ⟨subd4_5_121, List.forall_mem_cons.2 ⟨subd4_5_122, List.forall_mem_cons.2 ⟨subd4_5_123, List.forall_mem_cons.2 ⟨subd4_5_124, List.forall_mem_cons.2 ⟨subd4_5_125, List.forall_mem_cons.2 ⟨subd4_5_126, List.forall_mem_cons.2 ⟨subd4_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_128 : subd4_5 [1, 1, -1] = true := by decide +kernel
theorem subd4_5_129 : subd4_5 [1, 1, 0] = true := by decide +kernel
theorem subd4_5_130 : subd4_5 [1, 1, 1] = true := by decide +kernel
theorem subd4_5_131 : subd4_5 [1, 1, 2] = true := by decide +kernel
theorem subd4_5_132 : subd4_5 [1, 1, 3] = true := by decide +kernel
theorem subd4_5_133 : subd4_5 [1, 1, 4] = true := by decide +kernel
theorem subd4_5_134 : subd4_5 [1, 1, 5] = true := by decide +kernel
theorem subd4_5_135 : subd4_5 [1, 1, 6] = true := by decide +kernel
theorem subd4_5_136 : subd4_5 [1, 1, 7] = true := by decide +kernel
theorem sbd4_5_4 : ∀ q ∈ blkd4_5_4, subd4_5 q = true := by
  unfold blkd4_5_4
  exact List.forall_mem_cons.2 ⟨subd4_5_128, List.forall_mem_cons.2 ⟨subd4_5_129, List.forall_mem_cons.2 ⟨subd4_5_130, List.forall_mem_cons.2 ⟨subd4_5_131, List.forall_mem_cons.2 ⟨subd4_5_132, List.forall_mem_cons.2 ⟨subd4_5_133, List.forall_mem_cons.2 ⟨subd4_5_134, List.forall_mem_cons.2 ⟨subd4_5_135, List.forall_mem_cons.2 ⟨subd4_5_136, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-2] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [0] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-1, -2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1, -1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [-1, 0] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [-1, 1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [0, -2] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [0, -1] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [0, 0] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [0, 1] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [1, -2] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [1, -1] = true := by decide +kernel
theorem subd4_7_10 : subd4_7 [1, 0] = true := by decide +kernel
theorem subd4_7_11 : subd4_7 [1, 1] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_cons.2 ⟨subd4_7_10, List.forall_mem_cons.2 ⟨subd4_7_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_nil _⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_nil _⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_nil _⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_nil _⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C090
