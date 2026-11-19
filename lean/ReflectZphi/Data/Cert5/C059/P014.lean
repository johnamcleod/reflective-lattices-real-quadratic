import ReflectZphi.Data.Cert5.C059.Base

namespace ReflectZphi.Data.Cert5.C059
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_512 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_513 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_514 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_515 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_516 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_517 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_518 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_519 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_520 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_521 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_522 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_523 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_524 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_525 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_526 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_527 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_528 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_529 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_530 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_531 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_532 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_533 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_534 : sub7 [6] = true := by decide +kernel
theorem sb7_16 : ∀ q ∈ blk7_16, sub7 q = true := by
  unfold blk7_16
  exact List.forall_mem_cons.2 ⟨sub7_512, List.forall_mem_cons.2 ⟨sub7_513, List.forall_mem_cons.2 ⟨sub7_514, List.forall_mem_cons.2 ⟨sub7_515, List.forall_mem_cons.2 ⟨sub7_516, List.forall_mem_cons.2 ⟨sub7_517, List.forall_mem_cons.2 ⟨sub7_518, List.forall_mem_cons.2 ⟨sub7_519, List.forall_mem_cons.2 ⟨sub7_520, List.forall_mem_cons.2 ⟨sub7_521, List.forall_mem_cons.2 ⟨sub7_522, List.forall_mem_cons.2 ⟨sub7_523, List.forall_mem_cons.2 ⟨sub7_524, List.forall_mem_cons.2 ⟨sub7_525, List.forall_mem_cons.2 ⟨sub7_526, List.forall_mem_cons.2 ⟨sub7_527, List.forall_mem_cons.2 ⟨sub7_528, List.forall_mem_cons.2 ⟨sub7_529, List.forall_mem_cons.2 ⟨sub7_530, List.forall_mem_cons.2 ⟨sub7_531, List.forall_mem_cons.2 ⟨sub7_532, List.forall_mem_cons.2 ⟨sub7_533, List.forall_mem_cons.2 ⟨sub7_534, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C059
