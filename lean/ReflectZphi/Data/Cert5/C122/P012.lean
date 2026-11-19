import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_4_160 : subd6_4 [1, 1, -2] = true := by decide +kernel
theorem subd6_4_161 : subd6_4 [1, 1, -1] = true := by decide +kernel
theorem subd6_4_162 : subd6_4 [1, 1, 0] = true := by decide +kernel
theorem subd6_4_163 : subd6_4 [1, 1, 1] = true := by decide +kernel
theorem subd6_4_164 : subd6_4 [1, 1, 2] = true := by decide +kernel
theorem subd6_4_165 : subd6_4 [1, 1, 3] = true := by decide +kernel
theorem subd6_4_166 : subd6_4 [1, 1, 4] = true := by decide +kernel
theorem subd6_4_167 : subd6_4 [1, 1, 5] = true := by decide +kernel
theorem subd6_4_168 : subd6_4 [1, 1, 6] = true := by decide +kernel
theorem subd6_4_169 : subd6_4 [1, 1, 7] = true := by decide +kernel
theorem subd6_4_170 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_171 : subd6_4 [2, -2] = true := by decide +kernel
theorem subd6_4_172 : subd6_4 [2, -1] = true := by decide +kernel
theorem subd6_4_173 : subd6_4 [2, 0] = true := by decide +kernel
theorem subd6_4_174 : subd6_4 [2, 1] = true := by decide +kernel
theorem sbd6_4_5 : ∀ q ∈ blkd6_4_5, subd6_4 q = true := by
  unfold blkd6_4_5
  exact List.forall_mem_cons.2 ⟨subd6_4_160, List.forall_mem_cons.2 ⟨subd6_4_161, List.forall_mem_cons.2 ⟨subd6_4_162, List.forall_mem_cons.2 ⟨subd6_4_163, List.forall_mem_cons.2 ⟨subd6_4_164, List.forall_mem_cons.2 ⟨subd6_4_165, List.forall_mem_cons.2 ⟨subd6_4_166, List.forall_mem_cons.2 ⟨subd6_4_167, List.forall_mem_cons.2 ⟨subd6_4_168, List.forall_mem_cons.2 ⟨subd6_4_169, List.forall_mem_cons.2 ⟨subd6_4_170, List.forall_mem_cons.2 ⟨subd6_4_171, List.forall_mem_cons.2 ⟨subd6_4_172, List.forall_mem_cons.2 ⟨subd6_4_173, List.forall_mem_cons.2 ⟨subd6_4_174, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-1, -3] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [-1, -2] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [-1, -1] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [-1, 0] = true := by decide +kernel
theorem subd6_5_5 : subd6_5 [-1, 1] = true := by decide +kernel
theorem subd6_5_6 : subd6_5 [-1, 2] = true := by decide +kernel
theorem subd6_5_7 : subd6_5 [0, -3] = true := by decide +kernel
theorem subd6_5_8 : subd6_5 [0, -2] = true := by decide +kernel
theorem subd6_5_9 : subd6_5 [0, -1] = true := by decide +kernel
theorem subd6_5_10 : subd6_5 [0, 0] = true := by decide +kernel
theorem subd6_5_11 : subd6_5 [0, 1] = true := by decide +kernel
theorem subd6_5_12 : subd6_5 [0, 2] = true := by decide +kernel
theorem subd6_5_13 : subd6_5 [1, -3] = true := by decide +kernel
theorem subd6_5_14 : subd6_5 [1, -2] = true := by decide +kernel
theorem subd6_5_15 : subd6_5 [1, -1] = true := by decide +kernel
theorem subd6_5_16 : subd6_5 [1, 0] = true := by decide +kernel
theorem subd6_5_17 : subd6_5 [1, 1] = true := by decide +kernel
theorem subd6_5_18 : subd6_5 [1, 2] = true := by decide +kernel
theorem subd6_5_19 : subd6_5 [2] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_cons.2 ⟨subd6_5_5, List.forall_mem_cons.2 ⟨subd6_5_6, List.forall_mem_cons.2 ⟨subd6_5_7, List.forall_mem_cons.2 ⟨subd6_5_8, List.forall_mem_cons.2 ⟨subd6_5_9, List.forall_mem_cons.2 ⟨subd6_5_10, List.forall_mem_cons.2 ⟨subd6_5_11, List.forall_mem_cons.2 ⟨subd6_5_12, List.forall_mem_cons.2 ⟨subd6_5_13, List.forall_mem_cons.2 ⟨subd6_5_14, List.forall_mem_cons.2 ⟨subd6_5_15, List.forall_mem_cons.2 ⟨subd6_5_16, List.forall_mem_cons.2 ⟨subd6_5_17, List.forall_mem_cons.2 ⟨subd6_5_18, List.forall_mem_cons.2 ⟨subd6_5_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_nil _⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_nil _⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_nil _⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-2] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-1, -3] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-1, 1] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-1, 2] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [0, -3] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [0, 0] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [0, 2] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [1, -2] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [1, -1] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [1, 1] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [1, 2] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [2] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C122
