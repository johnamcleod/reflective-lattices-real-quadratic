import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-3] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-2, -3] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-2, -2] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-2, -1] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-2, 0] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-2, 1] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-2, 2] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-1, -4] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-1, -3] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-1, -2] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-1, -1] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-1, 0] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-1, 1] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-1, 2] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-1, 3] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [0, -4] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [0, -3] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [0, -2] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [0, -1] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [0, 0] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [0, 1] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [0, 2] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [0, 3] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [1, -4] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [1, -3] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [1, -2] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [1, -1] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [1, 0] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [1, 1] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [1, 2] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [1, 3] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [2, -3] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_32 : subd9_2 [2, -2] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [2, -1] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [2, 0] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [2, 1] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [2, 2] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [3] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-7] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-6, -6] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-6, -5] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-6, -4] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-6, -3] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-6, -2] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-6, -1] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-6, 0] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-5, -7] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-5, -6] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-5, -5] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-5, -4] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-5, -3] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-5, -2] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-5, -1] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-5, 0] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-5, 1] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-4, -7] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-4, -6] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-4, -5] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-4, -4] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-4, -3] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-4, -2] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-4, -1] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-4, 0] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-4, 1] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-4, 2] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-3, -7] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-3, -6] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-3, -5] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-3, -4] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-3, -3] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
