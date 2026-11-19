import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_7_0 : subd3_7 [-2] = true := by decide +kernel
theorem subd3_7_1 : subd3_7 [-1, -3] = true := by decide +kernel
theorem subd3_7_2 : subd3_7 [-1, -2] = true := by decide +kernel
theorem subd3_7_3 : subd3_7 [-1, -1] = true := by decide +kernel
theorem subd3_7_4 : subd3_7 [-1, 0] = true := by decide +kernel
theorem subd3_7_5 : subd3_7 [-1, 1] = true := by decide +kernel
theorem subd3_7_6 : subd3_7 [-1, 2] = true := by decide +kernel
theorem subd3_7_7 : subd3_7 [0, -3] = true := by decide +kernel
theorem subd3_7_8 : subd3_7 [0, -2] = true := by decide +kernel
theorem subd3_7_9 : subd3_7 [0, -1] = true := by decide +kernel
theorem subd3_7_10 : subd3_7 [0, 0] = true := by decide +kernel
theorem subd3_7_11 : subd3_7 [0, 1] = true := by decide +kernel
theorem subd3_7_12 : subd3_7 [0, 2] = true := by decide +kernel
theorem subd3_7_13 : subd3_7 [1, -3] = true := by decide +kernel
theorem subd3_7_14 : subd3_7 [1, -2] = true := by decide +kernel
theorem subd3_7_15 : subd3_7 [1, -1] = true := by decide +kernel
theorem subd3_7_16 : subd3_7 [1, 0] = true := by decide +kernel
theorem subd3_7_17 : subd3_7 [1, 1] = true := by decide +kernel
theorem subd3_7_18 : subd3_7 [1, 2] = true := by decide +kernel
theorem subd3_7_19 : subd3_7 [2] = true := by decide +kernel
theorem sbd3_7_0 : ∀ q ∈ blkd3_7_0, subd3_7 q = true := by
  unfold blkd3_7_0
  exact List.forall_mem_cons.2 ⟨subd3_7_0, List.forall_mem_cons.2 ⟨subd3_7_1, List.forall_mem_cons.2 ⟨subd3_7_2, List.forall_mem_cons.2 ⟨subd3_7_3, List.forall_mem_cons.2 ⟨subd3_7_4, List.forall_mem_cons.2 ⟨subd3_7_5, List.forall_mem_cons.2 ⟨subd3_7_6, List.forall_mem_cons.2 ⟨subd3_7_7, List.forall_mem_cons.2 ⟨subd3_7_8, List.forall_mem_cons.2 ⟨subd3_7_9, List.forall_mem_cons.2 ⟨subd3_7_10, List.forall_mem_cons.2 ⟨subd3_7_11, List.forall_mem_cons.2 ⟨subd3_7_12, List.forall_mem_cons.2 ⟨subd3_7_13, List.forall_mem_cons.2 ⟨subd3_7_14, List.forall_mem_cons.2 ⟨subd3_7_15, List.forall_mem_cons.2 ⟨subd3_7_16, List.forall_mem_cons.2 ⟨subd3_7_17, List.forall_mem_cons.2 ⟨subd3_7_18, List.forall_mem_cons.2 ⟨subd3_7_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-2] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-1, -4] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [0, 3] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [1, -4] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [2] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-1] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [1] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-3] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-1, -4] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [0, -4] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [1, 3] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [2] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [3] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_nil _⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-2] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-1] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [0] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [1] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [2] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
