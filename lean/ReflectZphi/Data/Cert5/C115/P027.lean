import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_nil _⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel
theorem subd17_2_0 : subd17_2 [] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_nil _⟩
theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_nil _⟩
theorem ld_okd17_4 : ldCheck G d17_4.U d17_4.ms ldd17_4 = true := by decide +kernel
theorem pre_okd17_4 : subPre G cell17 d17_4 = true := by decide +kernel
theorem subd17_4_0 : subd17_4 [-3] = true := by decide +kernel
theorem subd17_4_1 : subd17_4 [-2, -4] = true := by decide +kernel
theorem subd17_4_2 : subd17_4 [-2, -3] = true := by decide +kernel
theorem subd17_4_3 : subd17_4 [-2, -2] = true := by decide +kernel
theorem subd17_4_4 : subd17_4 [-2, -1] = true := by decide +kernel
theorem subd17_4_5 : subd17_4 [-2, 0] = true := by decide +kernel
theorem subd17_4_6 : subd17_4 [-2, 1] = true := by decide +kernel
theorem subd17_4_7 : subd17_4 [-2, 2] = true := by decide +kernel
theorem subd17_4_8 : subd17_4 [-1, -4] = true := by decide +kernel
theorem subd17_4_9 : subd17_4 [-1, -3] = true := by decide +kernel
theorem subd17_4_10 : subd17_4 [-1, -2] = true := by decide +kernel
theorem subd17_4_11 : subd17_4 [-1, -1] = true := by decide +kernel
theorem subd17_4_12 : subd17_4 [-1, 0] = true := by decide +kernel
theorem subd17_4_13 : subd17_4 [-1, 1] = true := by decide +kernel
theorem subd17_4_14 : subd17_4 [-1, 2] = true := by decide +kernel
theorem subd17_4_15 : subd17_4 [0, -4] = true := by decide +kernel
theorem subd17_4_16 : subd17_4 [0, -3] = true := by decide +kernel
theorem subd17_4_17 : subd17_4 [0, -2] = true := by decide +kernel
theorem subd17_4_18 : subd17_4 [0, -1] = true := by decide +kernel
theorem subd17_4_19 : subd17_4 [0, 0] = true := by decide +kernel
theorem subd17_4_20 : subd17_4 [0, 1] = true := by decide +kernel
theorem subd17_4_21 : subd17_4 [0, 2] = true := by decide +kernel
theorem subd17_4_22 : subd17_4 [0, 3] = true := by decide +kernel
theorem subd17_4_23 : subd17_4 [1, -3] = true := by decide +kernel
theorem subd17_4_24 : subd17_4 [1, -2] = true := by decide +kernel
theorem subd17_4_25 : subd17_4 [1, -1] = true := by decide +kernel
theorem subd17_4_26 : subd17_4 [1, 0] = true := by decide +kernel
theorem subd17_4_27 : subd17_4 [1, 1] = true := by decide +kernel
theorem subd17_4_28 : subd17_4 [1, 2] = true := by decide +kernel
theorem subd17_4_29 : subd17_4 [1, 3] = true := by decide +kernel
theorem subd17_4_30 : subd17_4 [2, -3] = true := by decide +kernel
theorem subd17_4_31 : subd17_4 [2, -2] = true := by decide +kernel
theorem sbd17_4_0 : ∀ q ∈ blkd17_4_0, subd17_4 q = true := by
  unfold blkd17_4_0
  exact List.forall_mem_cons.2 ⟨subd17_4_0, List.forall_mem_cons.2 ⟨subd17_4_1, List.forall_mem_cons.2 ⟨subd17_4_2, List.forall_mem_cons.2 ⟨subd17_4_3, List.forall_mem_cons.2 ⟨subd17_4_4, List.forall_mem_cons.2 ⟨subd17_4_5, List.forall_mem_cons.2 ⟨subd17_4_6, List.forall_mem_cons.2 ⟨subd17_4_7, List.forall_mem_cons.2 ⟨subd17_4_8, List.forall_mem_cons.2 ⟨subd17_4_9, List.forall_mem_cons.2 ⟨subd17_4_10, List.forall_mem_cons.2 ⟨subd17_4_11, List.forall_mem_cons.2 ⟨subd17_4_12, List.forall_mem_cons.2 ⟨subd17_4_13, List.forall_mem_cons.2 ⟨subd17_4_14, List.forall_mem_cons.2 ⟨subd17_4_15, List.forall_mem_cons.2 ⟨subd17_4_16, List.forall_mem_cons.2 ⟨subd17_4_17, List.forall_mem_cons.2 ⟨subd17_4_18, List.forall_mem_cons.2 ⟨subd17_4_19, List.forall_mem_cons.2 ⟨subd17_4_20, List.forall_mem_cons.2 ⟨subd17_4_21, List.forall_mem_cons.2 ⟨subd17_4_22, List.forall_mem_cons.2 ⟨subd17_4_23, List.forall_mem_cons.2 ⟨subd17_4_24, List.forall_mem_cons.2 ⟨subd17_4_25, List.forall_mem_cons.2 ⟨subd17_4_26, List.forall_mem_cons.2 ⟨subd17_4_27, List.forall_mem_cons.2 ⟨subd17_4_28, List.forall_mem_cons.2 ⟨subd17_4_29, List.forall_mem_cons.2 ⟨subd17_4_30, List.forall_mem_cons.2 ⟨subd17_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_4_32 : subd17_4 [2, -1] = true := by decide +kernel
theorem subd17_4_33 : subd17_4 [2, 0] = true := by decide +kernel
theorem subd17_4_34 : subd17_4 [2, 1] = true := by decide +kernel
theorem subd17_4_35 : subd17_4 [2, 2] = true := by decide +kernel
theorem subd17_4_36 : subd17_4 [2, 3] = true := by decide +kernel
theorem subd17_4_37 : subd17_4 [3] = true := by decide +kernel
theorem sbd17_4_1 : ∀ q ∈ blkd17_4_1, subd17_4 q = true := by
  unfold blkd17_4_1
  exact List.forall_mem_cons.2 ⟨subd17_4_32, List.forall_mem_cons.2 ⟨subd17_4_33, List.forall_mem_cons.2 ⟨subd17_4_34, List.forall_mem_cons.2 ⟨subd17_4_35, List.forall_mem_cons.2 ⟨subd17_4_36, List.forall_mem_cons.2 ⟨subd17_4_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd17_5 : ldCheck G d17_5.U d17_5.ms ldd17_5 = true := by decide +kernel
theorem pre_okd17_5 : subPre G cell17 d17_5 = true := by decide +kernel
theorem subd17_5_0 : subd17_5 [-2] = true := by decide +kernel
theorem subd17_5_1 : subd17_5 [-1] = true := by decide +kernel
theorem subd17_5_2 : subd17_5 [0] = true := by decide +kernel
theorem subd17_5_3 : subd17_5 [1] = true := by decide +kernel
theorem subd17_5_4 : subd17_5 [2] = true := by decide +kernel
theorem sbd17_5_0 : ∀ q ∈ blkd17_5_0, subd17_5 q = true := by
  unfold blkd17_5_0
  exact List.forall_mem_cons.2 ⟨subd17_5_0, List.forall_mem_cons.2 ⟨subd17_5_1, List.forall_mem_cons.2 ⟨subd17_5_2, List.forall_mem_cons.2 ⟨subd17_5_3, List.forall_mem_cons.2 ⟨subd17_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_6 : ldCheck G d17_6.U d17_6.ms ldd17_6 = true := by decide +kernel
theorem pre_okd17_6 : subPre G cell17 d17_6 = true := by decide +kernel
theorem subd17_6_0 : subd17_6 [-3] = true := by decide +kernel
theorem subd17_6_1 : subd17_6 [-2] = true := by decide +kernel
theorem subd17_6_2 : subd17_6 [-1, -3] = true := by decide +kernel
theorem subd17_6_3 : subd17_6 [-1, -2] = true := by decide +kernel
theorem subd17_6_4 : subd17_6 [-1, -1] = true := by decide +kernel
theorem subd17_6_5 : subd17_6 [-1, 0] = true := by decide +kernel
theorem subd17_6_6 : subd17_6 [-1, 1] = true := by decide +kernel
theorem subd17_6_7 : subd17_6 [-1, 2] = true := by decide +kernel
theorem subd17_6_8 : subd17_6 [-1, 3] = true := by decide +kernel
theorem subd17_6_9 : subd17_6 [0, -4] = true := by decide +kernel
theorem subd17_6_10 : subd17_6 [0, -3] = true := by decide +kernel
theorem subd17_6_11 : subd17_6 [0, -2] = true := by decide +kernel
theorem subd17_6_12 : subd17_6 [0, -1] = true := by decide +kernel
theorem subd17_6_13 : subd17_6 [0, 0] = true := by decide +kernel
theorem subd17_6_14 : subd17_6 [0, 1] = true := by decide +kernel
theorem subd17_6_15 : subd17_6 [0, 2] = true := by decide +kernel
theorem subd17_6_16 : subd17_6 [0, 3] = true := by decide +kernel
theorem subd17_6_17 : subd17_6 [1, -4] = true := by decide +kernel
theorem subd17_6_18 : subd17_6 [1, -3] = true := by decide +kernel
theorem subd17_6_19 : subd17_6 [1, -2] = true := by decide +kernel
theorem subd17_6_20 : subd17_6 [1, -1] = true := by decide +kernel
theorem subd17_6_21 : subd17_6 [1, 0] = true := by decide +kernel
theorem subd17_6_22 : subd17_6 [1, 1] = true := by decide +kernel
theorem subd17_6_23 : subd17_6 [1, 2] = true := by decide +kernel
theorem subd17_6_24 : subd17_6 [2] = true := by decide +kernel
theorem subd17_6_25 : subd17_6 [3] = true := by decide +kernel
theorem sbd17_6_0 : ∀ q ∈ blkd17_6_0, subd17_6 q = true := by
  unfold blkd17_6_0
  exact List.forall_mem_cons.2 ⟨subd17_6_0, List.forall_mem_cons.2 ⟨subd17_6_1, List.forall_mem_cons.2 ⟨subd17_6_2, List.forall_mem_cons.2 ⟨subd17_6_3, List.forall_mem_cons.2 ⟨subd17_6_4, List.forall_mem_cons.2 ⟨subd17_6_5, List.forall_mem_cons.2 ⟨subd17_6_6, List.forall_mem_cons.2 ⟨subd17_6_7, List.forall_mem_cons.2 ⟨subd17_6_8, List.forall_mem_cons.2 ⟨subd17_6_9, List.forall_mem_cons.2 ⟨subd17_6_10, List.forall_mem_cons.2 ⟨subd17_6_11, List.forall_mem_cons.2 ⟨subd17_6_12, List.forall_mem_cons.2 ⟨subd17_6_13, List.forall_mem_cons.2 ⟨subd17_6_14, List.forall_mem_cons.2 ⟨subd17_6_15, List.forall_mem_cons.2 ⟨subd17_6_16, List.forall_mem_cons.2 ⟨subd17_6_17, List.forall_mem_cons.2 ⟨subd17_6_18, List.forall_mem_cons.2 ⟨subd17_6_19, List.forall_mem_cons.2 ⟨subd17_6_20, List.forall_mem_cons.2 ⟨subd17_6_21, List.forall_mem_cons.2 ⟨subd17_6_22, List.forall_mem_cons.2 ⟨subd17_6_23, List.forall_mem_cons.2 ⟨subd17_6_24, List.forall_mem_cons.2 ⟨subd17_6_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
