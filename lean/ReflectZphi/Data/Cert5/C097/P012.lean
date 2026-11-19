import ReflectZphi.Data.Cert5.C097.Base

namespace ReflectZphi.Data.Cert5.C097
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_0 : sub11 [-2] = true := by decide +kernel
theorem sub11_1 : sub11 [-1, -3] = true := by decide +kernel
theorem sub11_2 : sub11 [-1, -2] = true := by decide +kernel
theorem sub11_3 : sub11 [-1, -1] = true := by decide +kernel
theorem sub11_4 : sub11 [-1, 0] = true := by decide +kernel
theorem sub11_5 : sub11 [-1, 1] = true := by decide +kernel
theorem sub11_6 : sub11 [-1, 2] = true := by decide +kernel
theorem sub11_7 : sub11 [0, -3] = true := by decide +kernel
theorem sub11_8 : sub11 [0, -2] = true := by decide +kernel
theorem sub11_9 : sub11 [0, -1] = true := by decide +kernel
theorem sub11_10 : sub11 [0, 0] = true := by decide +kernel
theorem sub11_11 : sub11 [0, 1] = true := by decide +kernel
theorem sub11_12 : sub11 [0, 2] = true := by decide +kernel
theorem sub11_13 : sub11 [1, -3] = true := by decide +kernel
theorem sub11_14 : sub11 [1, -2] = true := by decide +kernel
theorem sub11_15 : sub11 [1, -1] = true := by decide +kernel
theorem sub11_16 : sub11 [1, 0] = true := by decide +kernel
theorem sub11_17 : sub11 [1, 1] = true := by decide +kernel
theorem sub11_18 : sub11 [1, 2] = true := by decide +kernel
theorem sub11_19 : sub11 [2] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C097
