import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_13 : ldCheck G d13_13.U d13_13.ms ldd13_13 = true := by decide +kernel
theorem pre_okd13_13 : subPre G cell13 d13_13 = true := by decide +kernel
theorem subd13_13_0 : subd13_13 [-2] = true := by decide +kernel
theorem subd13_13_1 : subd13_13 [-1] = true := by decide +kernel
theorem subd13_13_2 : subd13_13 [0] = true := by decide +kernel
theorem subd13_13_3 : subd13_13 [1] = true := by decide +kernel
theorem subd13_13_4 : subd13_13 [2] = true := by decide +kernel
theorem sbd13_13_0 : ∀ q ∈ blkd13_13_0, subd13_13 q = true := by
  unfold blkd13_13_0
  exact List.forall_mem_cons.2 ⟨subd13_13_0, List.forall_mem_cons.2 ⟨subd13_13_1, List.forall_mem_cons.2 ⟨subd13_13_2, List.forall_mem_cons.2 ⟨subd13_13_3, List.forall_mem_cons.2 ⟨subd13_13_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_14 : ldCheck G d13_14.U d13_14.ms ldd13_14 = true := by decide +kernel
theorem pre_okd13_14 : subPre G cell13 d13_14 = true := by decide +kernel
theorem subd13_14_0 : subd13_14 [-3] = true := by decide +kernel
theorem subd13_14_1 : subd13_14 [-2, -3] = true := by decide +kernel
theorem subd13_14_2 : subd13_14 [-2, -2] = true := by decide +kernel
theorem subd13_14_3 : subd13_14 [-2, -1] = true := by decide +kernel
theorem subd13_14_4 : subd13_14 [-2, 0] = true := by decide +kernel
theorem subd13_14_5 : subd13_14 [-2, 1] = true := by decide +kernel
theorem subd13_14_6 : subd13_14 [-2, 2] = true := by decide +kernel
theorem subd13_14_7 : subd13_14 [-2, 3] = true := by decide +kernel
theorem subd13_14_8 : subd13_14 [-2, 4] = true := by decide +kernel
theorem subd13_14_9 : subd13_14 [-1, -4] = true := by decide +kernel
theorem subd13_14_10 : subd13_14 [-1, -3] = true := by decide +kernel
theorem subd13_14_11 : subd13_14 [-1, -2] = true := by decide +kernel
theorem subd13_14_12 : subd13_14 [-1, -1] = true := by decide +kernel
theorem subd13_14_13 : subd13_14 [-1, 0] = true := by decide +kernel
theorem subd13_14_14 : subd13_14 [-1, 1] = true := by decide +kernel
theorem subd13_14_15 : subd13_14 [-1, 2] = true := by decide +kernel
theorem subd13_14_16 : subd13_14 [-1, 3] = true := by decide +kernel
theorem subd13_14_17 : subd13_14 [-1, 4] = true := by decide +kernel
theorem subd13_14_18 : subd13_14 [0, -4] = true := by decide +kernel
theorem subd13_14_19 : subd13_14 [0, -3] = true := by decide +kernel
theorem subd13_14_20 : subd13_14 [0, -2] = true := by decide +kernel
theorem subd13_14_21 : subd13_14 [0, -1] = true := by decide +kernel
theorem subd13_14_22 : subd13_14 [0, 0] = true := by decide +kernel
theorem subd13_14_23 : subd13_14 [0, 1] = true := by decide +kernel
theorem subd13_14_24 : subd13_14 [0, 2] = true := by decide +kernel
theorem subd13_14_25 : subd13_14 [0, 3] = true := by decide +kernel
theorem subd13_14_26 : subd13_14 [1, -5] = true := by decide +kernel
theorem subd13_14_27 : subd13_14 [1, -4] = true := by decide +kernel
theorem subd13_14_28 : subd13_14 [1, -3] = true := by decide +kernel
theorem subd13_14_29 : subd13_14 [1, -2] = true := by decide +kernel
theorem subd13_14_30 : subd13_14 [1, -1] = true := by decide +kernel
theorem subd13_14_31 : subd13_14 [1, 0] = true := by decide +kernel
theorem sbd13_14_0 : ∀ q ∈ blkd13_14_0, subd13_14 q = true := by
  unfold blkd13_14_0
  exact List.forall_mem_cons.2 ⟨subd13_14_0, List.forall_mem_cons.2 ⟨subd13_14_1, List.forall_mem_cons.2 ⟨subd13_14_2, List.forall_mem_cons.2 ⟨subd13_14_3, List.forall_mem_cons.2 ⟨subd13_14_4, List.forall_mem_cons.2 ⟨subd13_14_5, List.forall_mem_cons.2 ⟨subd13_14_6, List.forall_mem_cons.2 ⟨subd13_14_7, List.forall_mem_cons.2 ⟨subd13_14_8, List.forall_mem_cons.2 ⟨subd13_14_9, List.forall_mem_cons.2 ⟨subd13_14_10, List.forall_mem_cons.2 ⟨subd13_14_11, List.forall_mem_cons.2 ⟨subd13_14_12, List.forall_mem_cons.2 ⟨subd13_14_13, List.forall_mem_cons.2 ⟨subd13_14_14, List.forall_mem_cons.2 ⟨subd13_14_15, List.forall_mem_cons.2 ⟨subd13_14_16, List.forall_mem_cons.2 ⟨subd13_14_17, List.forall_mem_cons.2 ⟨subd13_14_18, List.forall_mem_cons.2 ⟨subd13_14_19, List.forall_mem_cons.2 ⟨subd13_14_20, List.forall_mem_cons.2 ⟨subd13_14_21, List.forall_mem_cons.2 ⟨subd13_14_22, List.forall_mem_cons.2 ⟨subd13_14_23, List.forall_mem_cons.2 ⟨subd13_14_24, List.forall_mem_cons.2 ⟨subd13_14_25, List.forall_mem_cons.2 ⟨subd13_14_26, List.forall_mem_cons.2 ⟨subd13_14_27, List.forall_mem_cons.2 ⟨subd13_14_28, List.forall_mem_cons.2 ⟨subd13_14_29, List.forall_mem_cons.2 ⟨subd13_14_30, List.forall_mem_cons.2 ⟨subd13_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_14_32 : subd13_14 [1, 1] = true := by decide +kernel
theorem subd13_14_33 : subd13_14 [1, 2] = true := by decide +kernel
theorem subd13_14_34 : subd13_14 [1, 3] = true := by decide +kernel
theorem subd13_14_35 : subd13_14 [2, -5] = true := by decide +kernel
theorem subd13_14_36 : subd13_14 [2, -4] = true := by decide +kernel
theorem subd13_14_37 : subd13_14 [2, -3] = true := by decide +kernel
theorem subd13_14_38 : subd13_14 [2, -2] = true := by decide +kernel
theorem subd13_14_39 : subd13_14 [2, -1] = true := by decide +kernel
theorem subd13_14_40 : subd13_14 [2, 0] = true := by decide +kernel
theorem subd13_14_41 : subd13_14 [2, 1] = true := by decide +kernel
theorem subd13_14_42 : subd13_14 [2, 2] = true := by decide +kernel
theorem subd13_14_43 : subd13_14 [3] = true := by decide +kernel
theorem sbd13_14_1 : ∀ q ∈ blkd13_14_1, subd13_14 q = true := by
  unfold blkd13_14_1
  exact List.forall_mem_cons.2 ⟨subd13_14_32, List.forall_mem_cons.2 ⟨subd13_14_33, List.forall_mem_cons.2 ⟨subd13_14_34, List.forall_mem_cons.2 ⟨subd13_14_35, List.forall_mem_cons.2 ⟨subd13_14_36, List.forall_mem_cons.2 ⟨subd13_14_37, List.forall_mem_cons.2 ⟨subd13_14_38, List.forall_mem_cons.2 ⟨subd13_14_39, List.forall_mem_cons.2 ⟨subd13_14_40, List.forall_mem_cons.2 ⟨subd13_14_41, List.forall_mem_cons.2 ⟨subd13_14_42, List.forall_mem_cons.2 ⟨subd13_14_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
