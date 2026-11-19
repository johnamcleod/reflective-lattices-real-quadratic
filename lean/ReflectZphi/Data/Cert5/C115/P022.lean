import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_4 : ldCheck G d14_4.U d14_4.ms ldd14_4 = true := by decide +kernel
theorem pre_okd14_4 : subPre G cell14 d14_4 = true := by decide +kernel
theorem subd14_4_0 : subd14_4 [-3] = true := by decide +kernel
theorem subd14_4_1 : subd14_4 [-2] = true := by decide +kernel
theorem subd14_4_2 : subd14_4 [-1, -3] = true := by decide +kernel
theorem subd14_4_3 : subd14_4 [-1, -2] = true := by decide +kernel
theorem subd14_4_4 : subd14_4 [-1, -1] = true := by decide +kernel
theorem subd14_4_5 : subd14_4 [-1, 0] = true := by decide +kernel
theorem subd14_4_6 : subd14_4 [-1, 1] = true := by decide +kernel
theorem subd14_4_7 : subd14_4 [-1, 2] = true := by decide +kernel
theorem subd14_4_8 : subd14_4 [-1, 3] = true := by decide +kernel
theorem subd14_4_9 : subd14_4 [0, -3] = true := by decide +kernel
theorem subd14_4_10 : subd14_4 [0, -2] = true := by decide +kernel
theorem subd14_4_11 : subd14_4 [0, -1] = true := by decide +kernel
theorem subd14_4_12 : subd14_4 [0, 0] = true := by decide +kernel
theorem subd14_4_13 : subd14_4 [0, 1] = true := by decide +kernel
theorem subd14_4_14 : subd14_4 [0, 2] = true := by decide +kernel
theorem subd14_4_15 : subd14_4 [1, -4] = true := by decide +kernel
theorem subd14_4_16 : subd14_4 [1, -3] = true := by decide +kernel
theorem subd14_4_17 : subd14_4 [1, -2] = true := by decide +kernel
theorem subd14_4_18 : subd14_4 [1, -1] = true := by decide +kernel
theorem subd14_4_19 : subd14_4 [1, 0] = true := by decide +kernel
theorem subd14_4_20 : subd14_4 [1, 1] = true := by decide +kernel
theorem subd14_4_21 : subd14_4 [1, 2] = true := by decide +kernel
theorem subd14_4_22 : subd14_4 [2] = true := by decide +kernel
theorem subd14_4_23 : subd14_4 [3] = true := by decide +kernel
theorem sbd14_4_0 : ∀ q ∈ blkd14_4_0, subd14_4 q = true := by
  unfold blkd14_4_0
  exact List.forall_mem_cons.2 ⟨subd14_4_0, List.forall_mem_cons.2 ⟨subd14_4_1, List.forall_mem_cons.2 ⟨subd14_4_2, List.forall_mem_cons.2 ⟨subd14_4_3, List.forall_mem_cons.2 ⟨subd14_4_4, List.forall_mem_cons.2 ⟨subd14_4_5, List.forall_mem_cons.2 ⟨subd14_4_6, List.forall_mem_cons.2 ⟨subd14_4_7, List.forall_mem_cons.2 ⟨subd14_4_8, List.forall_mem_cons.2 ⟨subd14_4_9, List.forall_mem_cons.2 ⟨subd14_4_10, List.forall_mem_cons.2 ⟨subd14_4_11, List.forall_mem_cons.2 ⟨subd14_4_12, List.forall_mem_cons.2 ⟨subd14_4_13, List.forall_mem_cons.2 ⟨subd14_4_14, List.forall_mem_cons.2 ⟨subd14_4_15, List.forall_mem_cons.2 ⟨subd14_4_16, List.forall_mem_cons.2 ⟨subd14_4_17, List.forall_mem_cons.2 ⟨subd14_4_18, List.forall_mem_cons.2 ⟨subd14_4_19, List.forall_mem_cons.2 ⟨subd14_4_20, List.forall_mem_cons.2 ⟨subd14_4_21, List.forall_mem_cons.2 ⟨subd14_4_22, List.forall_mem_cons.2 ⟨subd14_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_5 : ldCheck G d14_5.U d14_5.ms ldd14_5 = true := by decide +kernel
theorem pre_okd14_5 : subPre G cell14 d14_5 = true := by decide +kernel
theorem subd14_5_0 : subd14_5 [-2] = true := by decide +kernel
theorem subd14_5_1 : subd14_5 [-1] = true := by decide +kernel
theorem subd14_5_2 : subd14_5 [0] = true := by decide +kernel
theorem subd14_5_3 : subd14_5 [1] = true := by decide +kernel
theorem subd14_5_4 : subd14_5 [2] = true := by decide +kernel
theorem sbd14_5_0 : ∀ q ∈ blkd14_5_0, subd14_5 q = true := by
  unfold blkd14_5_0
  exact List.forall_mem_cons.2 ⟨subd14_5_0, List.forall_mem_cons.2 ⟨subd14_5_1, List.forall_mem_cons.2 ⟨subd14_5_2, List.forall_mem_cons.2 ⟨subd14_5_3, List.forall_mem_cons.2 ⟨subd14_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_6 : ldCheck G d14_6.U d14_6.ms ldd14_6 = true := by decide +kernel
theorem pre_okd14_6 : subPre G cell14 d14_6 = true := by decide +kernel
theorem subd14_6_0 : subd14_6 [-3] = true := by decide +kernel
theorem subd14_6_1 : subd14_6 [-2] = true := by decide +kernel
theorem subd14_6_2 : subd14_6 [-1] = true := by decide +kernel
theorem subd14_6_3 : subd14_6 [0] = true := by decide +kernel
theorem subd14_6_4 : subd14_6 [1] = true := by decide +kernel
theorem subd14_6_5 : subd14_6 [2] = true := by decide +kernel
theorem subd14_6_6 : subd14_6 [3] = true := by decide +kernel
theorem sbd14_6_0 : ∀ q ∈ blkd14_6_0, subd14_6 q = true := by
  unfold blkd14_6_0
  exact List.forall_mem_cons.2 ⟨subd14_6_0, List.forall_mem_cons.2 ⟨subd14_6_1, List.forall_mem_cons.2 ⟨subd14_6_2, List.forall_mem_cons.2 ⟨subd14_6_3, List.forall_mem_cons.2 ⟨subd14_6_4, List.forall_mem_cons.2 ⟨subd14_6_5, List.forall_mem_cons.2 ⟨subd14_6_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_7 : ldCheck G d14_7.U d14_7.ms ldd14_7 = true := by decide +kernel
theorem pre_okd14_7 : subPre G cell14 d14_7 = true := by decide +kernel
theorem subd14_7_0 : subd14_7 [-1] = true := by decide +kernel
theorem subd14_7_1 : subd14_7 [0] = true := by decide +kernel
theorem subd14_7_2 : subd14_7 [1] = true := by decide +kernel
theorem sbd14_7_0 : ∀ q ∈ blkd14_7_0, subd14_7 q = true := by
  unfold blkd14_7_0
  exact List.forall_mem_cons.2 ⟨subd14_7_0, List.forall_mem_cons.2 ⟨subd14_7_1, List.forall_mem_cons.2 ⟨subd14_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_8 : ldCheck G d14_8.U d14_8.ms ldd14_8 = true := by decide +kernel
theorem pre_okd14_8 : subPre G cell14 d14_8 = true := by decide +kernel
theorem subd14_8_0 : subd14_8 [-2] = true := by decide +kernel
theorem subd14_8_1 : subd14_8 [-1] = true := by decide +kernel
theorem subd14_8_2 : subd14_8 [0] = true := by decide +kernel
theorem subd14_8_3 : subd14_8 [1] = true := by decide +kernel
theorem subd14_8_4 : subd14_8 [2] = true := by decide +kernel
theorem sbd14_8_0 : ∀ q ∈ blkd14_8_0, subd14_8 q = true := by
  unfold blkd14_8_0
  exact List.forall_mem_cons.2 ⟨subd14_8_0, List.forall_mem_cons.2 ⟨subd14_8_1, List.forall_mem_cons.2 ⟨subd14_8_2, List.forall_mem_cons.2 ⟨subd14_8_3, List.forall_mem_cons.2 ⟨subd14_8_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_9 : ldCheck G d14_9.U d14_9.ms ldd14_9 = true := by decide +kernel
theorem pre_okd14_9 : subPre G cell14 d14_9 = true := by decide +kernel
theorem subd14_9_0 : subd14_9 [] = true := by decide +kernel
theorem sbd14_9_0 : ∀ q ∈ blkd14_9_0, subd14_9 q = true := by
  unfold blkd14_9_0
  exact List.forall_mem_cons.2 ⟨subd14_9_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
