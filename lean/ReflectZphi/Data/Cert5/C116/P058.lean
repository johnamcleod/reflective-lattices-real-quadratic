import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_1_0 : subd16_1 [-4] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [-3] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [-2, -2] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [-2, -1] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [-2, 0] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [-2, 1] = true := by decide +kernel
theorem subd16_1_6 : subd16_1 [-2, 2] = true := by decide +kernel
theorem subd16_1_7 : subd16_1 [-2, 3] = true := by decide +kernel
theorem subd16_1_8 : subd16_1 [-1, -3] = true := by decide +kernel
theorem subd16_1_9 : subd16_1 [-1, -2] = true := by decide +kernel
theorem subd16_1_10 : subd16_1 [-1, -1] = true := by decide +kernel
theorem subd16_1_11 : subd16_1 [-1, 0] = true := by decide +kernel
theorem subd16_1_12 : subd16_1 [-1, 1] = true := by decide +kernel
theorem subd16_1_13 : subd16_1 [-1, 2] = true := by decide +kernel
theorem subd16_1_14 : subd16_1 [-1, 3] = true := by decide +kernel
theorem subd16_1_15 : subd16_1 [0, -4] = true := by decide +kernel
theorem subd16_1_16 : subd16_1 [0, -3] = true := by decide +kernel
theorem subd16_1_17 : subd16_1 [0, -2] = true := by decide +kernel
theorem subd16_1_18 : subd16_1 [0, -1] = true := by decide +kernel
theorem subd16_1_19 : subd16_1 [0, 0] = true := by decide +kernel
theorem subd16_1_20 : subd16_1 [0, 1] = true := by decide +kernel
theorem subd16_1_21 : subd16_1 [0, 2] = true := by decide +kernel
theorem subd16_1_22 : subd16_1 [0, 3] = true := by decide +kernel
theorem subd16_1_23 : subd16_1 [1, -4] = true := by decide +kernel
theorem subd16_1_24 : subd16_1 [1, -3] = true := by decide +kernel
theorem subd16_1_25 : subd16_1 [1, -2] = true := by decide +kernel
theorem subd16_1_26 : subd16_1 [1, -1] = true := by decide +kernel
theorem subd16_1_27 : subd16_1 [1, 0] = true := by decide +kernel
theorem subd16_1_28 : subd16_1 [1, 1] = true := by decide +kernel
theorem subd16_1_29 : subd16_1 [1, 2] = true := by decide +kernel
theorem subd16_1_30 : subd16_1 [2, -4] = true := by decide +kernel
theorem subd16_1_31 : subd16_1 [2, -3] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_cons.2 ⟨subd16_1_6, List.forall_mem_cons.2 ⟨subd16_1_7, List.forall_mem_cons.2 ⟨subd16_1_8, List.forall_mem_cons.2 ⟨subd16_1_9, List.forall_mem_cons.2 ⟨subd16_1_10, List.forall_mem_cons.2 ⟨subd16_1_11, List.forall_mem_cons.2 ⟨subd16_1_12, List.forall_mem_cons.2 ⟨subd16_1_13, List.forall_mem_cons.2 ⟨subd16_1_14, List.forall_mem_cons.2 ⟨subd16_1_15, List.forall_mem_cons.2 ⟨subd16_1_16, List.forall_mem_cons.2 ⟨subd16_1_17, List.forall_mem_cons.2 ⟨subd16_1_18, List.forall_mem_cons.2 ⟨subd16_1_19, List.forall_mem_cons.2 ⟨subd16_1_20, List.forall_mem_cons.2 ⟨subd16_1_21, List.forall_mem_cons.2 ⟨subd16_1_22, List.forall_mem_cons.2 ⟨subd16_1_23, List.forall_mem_cons.2 ⟨subd16_1_24, List.forall_mem_cons.2 ⟨subd16_1_25, List.forall_mem_cons.2 ⟨subd16_1_26, List.forall_mem_cons.2 ⟨subd16_1_27, List.forall_mem_cons.2 ⟨subd16_1_28, List.forall_mem_cons.2 ⟨subd16_1_29, List.forall_mem_cons.2 ⟨subd16_1_30, List.forall_mem_cons.2 ⟨subd16_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_32 : subd16_1 [2, -2] = true := by decide +kernel
theorem subd16_1_33 : subd16_1 [2, -1] = true := by decide +kernel
theorem subd16_1_34 : subd16_1 [2, 0] = true := by decide +kernel
theorem subd16_1_35 : subd16_1 [2, 1] = true := by decide +kernel
theorem subd16_1_36 : subd16_1 [3] = true := by decide +kernel
theorem subd16_1_37 : subd16_1 [4] = true := by decide +kernel
theorem sbd16_1_1 : ∀ q ∈ blkd16_1_1, subd16_1 q = true := by
  unfold blkd16_1_1
  exact List.forall_mem_cons.2 ⟨subd16_1_32, List.forall_mem_cons.2 ⟨subd16_1_33, List.forall_mem_cons.2 ⟨subd16_1_34, List.forall_mem_cons.2 ⟨subd16_1_35, List.forall_mem_cons.2 ⟨subd16_1_36, List.forall_mem_cons.2 ⟨subd16_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
