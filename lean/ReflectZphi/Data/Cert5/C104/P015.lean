import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub12_0 : sub12 [-3] = true := by decide +kernel
theorem sub12_1 : sub12 [-2, -2] = true := by decide +kernel
theorem sub12_2 : sub12 [-2, -1] = true := by decide +kernel
theorem sub12_3 : sub12 [-2, 0] = true := by decide +kernel
theorem sub12_4 : sub12 [-2, 1] = true := by decide +kernel
theorem sub12_5 : sub12 [-2, 2] = true := by decide +kernel
theorem sub12_6 : sub12 [-2, 3] = true := by decide +kernel
theorem sub12_7 : sub12 [-1, -3] = true := by decide +kernel
theorem sub12_8 : sub12 [-1, -2] = true := by decide +kernel
theorem sub12_9 : sub12 [-1, -1] = true := by decide +kernel
theorem sub12_10 : sub12 [-1, 0] = true := by decide +kernel
theorem sub12_11 : sub12 [-1, 1] = true := by decide +kernel
theorem sub12_12 : sub12 [-1, 2] = true := by decide +kernel
theorem sub12_13 : sub12 [-1, 3] = true := by decide +kernel
theorem sub12_14 : sub12 [0, -4] = true := by decide +kernel
theorem sub12_15 : sub12 [0, -3] = true := by decide +kernel
theorem sub12_16 : sub12 [0, -2] = true := by decide +kernel
theorem sub12_17 : sub12 [0, -1] = true := by decide +kernel
theorem sub12_18 : sub12 [0, 0] = true := by decide +kernel
theorem sub12_19 : sub12 [0, 1] = true := by decide +kernel
theorem sub12_20 : sub12 [0, 2] = true := by decide +kernel
theorem sub12_21 : sub12 [0, 3] = true := by decide +kernel
theorem sub12_22 : sub12 [1, -4] = true := by decide +kernel
theorem sub12_23 : sub12 [1, -3] = true := by decide +kernel
theorem sub12_24 : sub12 [1, -2] = true := by decide +kernel
theorem sub12_25 : sub12 [1, -1] = true := by decide +kernel
theorem sub12_26 : sub12 [1, 0] = true := by decide +kernel
theorem sub12_27 : sub12 [1, 1] = true := by decide +kernel
theorem sub12_28 : sub12 [1, 2] = true := by decide +kernel
theorem sub12_29 : sub12 [2, -4] = true := by decide +kernel
theorem sub12_30 : sub12 [2, -3] = true := by decide +kernel
theorem sub12_31 : sub12 [2, -2] = true := by decide +kernel
theorem sb12_0 : ∀ q ∈ blk12_0, sub12 q = true := by
  unfold blk12_0
  exact List.forall_mem_cons.2 ⟨sub12_0, List.forall_mem_cons.2 ⟨sub12_1, List.forall_mem_cons.2 ⟨sub12_2, List.forall_mem_cons.2 ⟨sub12_3, List.forall_mem_cons.2 ⟨sub12_4, List.forall_mem_cons.2 ⟨sub12_5, List.forall_mem_cons.2 ⟨sub12_6, List.forall_mem_cons.2 ⟨sub12_7, List.forall_mem_cons.2 ⟨sub12_8, List.forall_mem_cons.2 ⟨sub12_9, List.forall_mem_cons.2 ⟨sub12_10, List.forall_mem_cons.2 ⟨sub12_11, List.forall_mem_cons.2 ⟨sub12_12, List.forall_mem_cons.2 ⟨sub12_13, List.forall_mem_cons.2 ⟨sub12_14, List.forall_mem_cons.2 ⟨sub12_15, List.forall_mem_cons.2 ⟨sub12_16, List.forall_mem_cons.2 ⟨sub12_17, List.forall_mem_cons.2 ⟨sub12_18, List.forall_mem_cons.2 ⟨sub12_19, List.forall_mem_cons.2 ⟨sub12_20, List.forall_mem_cons.2 ⟨sub12_21, List.forall_mem_cons.2 ⟨sub12_22, List.forall_mem_cons.2 ⟨sub12_23, List.forall_mem_cons.2 ⟨sub12_24, List.forall_mem_cons.2 ⟨sub12_25, List.forall_mem_cons.2 ⟨sub12_26, List.forall_mem_cons.2 ⟨sub12_27, List.forall_mem_cons.2 ⟨sub12_28, List.forall_mem_cons.2 ⟨sub12_29, List.forall_mem_cons.2 ⟨sub12_30, List.forall_mem_cons.2 ⟨sub12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_32 : sub12 [2, -1] = true := by decide +kernel
theorem sub12_33 : sub12 [2, 0] = true := by decide +kernel
theorem sub12_34 : sub12 [2, 1] = true := by decide +kernel
theorem sub12_35 : sub12 [3] = true := by decide +kernel
theorem sb12_1 : ∀ q ∈ blk12_1, sub12 q = true := by
  unfold blk12_1
  exact List.forall_mem_cons.2 ⟨sub12_32, List.forall_mem_cons.2 ⟨sub12_33, List.forall_mem_cons.2 ⟨sub12_34, List.forall_mem_cons.2 ⟨sub12_35, List.forall_mem_nil _⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
