import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_32 : sub8 [0, -1] = true := by decide +kernel
theorem sub8_33 : sub8 [0, 0] = true := by decide +kernel
theorem sub8_34 : sub8 [0, 1] = true := by decide +kernel
theorem sub8_35 : sub8 [0, 2] = true := by decide +kernel
theorem sub8_36 : sub8 [0, 3] = true := by decide +kernel
theorem sub8_37 : sub8 [0, 4] = true := by decide +kernel
theorem sub8_38 : sub8 [1, -5] = true := by decide +kernel
theorem sub8_39 : sub8 [1, -4] = true := by decide +kernel
theorem sub8_40 : sub8 [1, -3] = true := by decide +kernel
theorem sub8_41 : sub8 [1, -2] = true := by decide +kernel
theorem sub8_42 : sub8 [1, -1] = true := by decide +kernel
theorem sub8_43 : sub8 [1, 0] = true := by decide +kernel
theorem sub8_44 : sub8 [1, 1] = true := by decide +kernel
theorem sub8_45 : sub8 [1, 2] = true := by decide +kernel
theorem sub8_46 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_47 : sub8 [1, 4] = true := by decide +kernel
theorem sub8_48 : sub8 [2, -5] = true := by decide +kernel
theorem sub8_49 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_50 : sub8 [2, -3] = true := by decide +kernel
theorem sub8_51 : sub8 [2, -2] = true := by decide +kernel
theorem sub8_52 : sub8 [2, -1] = true := by decide +kernel
theorem sub8_53 : sub8 [2, 0] = true := by decide +kernel
theorem sub8_54 : sub8 [2, 1] = true := by decide +kernel
theorem sub8_55 : sub8 [2, 2] = true := by decide +kernel
theorem sub8_56 : sub8 [2, 3] = true := by decide +kernel
theorem sub8_57 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_58 : sub8 [3, -3] = true := by decide +kernel
theorem sub8_59 : sub8 [3, -2] = true := by decide +kernel
theorem sub8_60 : sub8 [3, -1] = true := by decide +kernel
theorem sub8_61 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_62 : sub8 [3, 1] = true := by decide +kernel
theorem sub8_63 : sub8 [3, 2] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_65 : sub8 [4] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_nil _⟩⟩
theorem sub9_0 : sub9 [-3] = true := by decide +kernel
theorem sub9_1 : sub9 [-2] = true := by decide +kernel
theorem sub9_2 : sub9 [-1, -4] = true := by decide +kernel
theorem sub9_3 : sub9 [-1, -3] = true := by decide +kernel
theorem sub9_4 : sub9 [-1, -2] = true := by decide +kernel
theorem sub9_5 : sub9 [-1, -1] = true := by decide +kernel
theorem sub9_6 : sub9 [-1, 0] = true := by decide +kernel
theorem sub9_7 : sub9 [-1, 1] = true := by decide +kernel
theorem sub9_8 : sub9 [-1, 2] = true := by decide +kernel
theorem sub9_9 : sub9 [-1, 3] = true := by decide +kernel
theorem sub9_10 : sub9 [-1, 4] = true := by decide +kernel
theorem sub9_11 : sub9 [0, -4] = true := by decide +kernel
theorem sub9_12 : sub9 [0, -3] = true := by decide +kernel
theorem sub9_13 : sub9 [0, -2] = true := by decide +kernel
theorem sub9_14 : sub9 [0, -1] = true := by decide +kernel
theorem sub9_15 : sub9 [0, 0] = true := by decide +kernel
theorem sub9_16 : sub9 [0, 1] = true := by decide +kernel
theorem sub9_17 : sub9 [0, 2] = true := by decide +kernel
theorem sub9_18 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_19 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_20 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_21 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_22 : sub9 [1, -2] = true := by decide +kernel
theorem sub9_23 : sub9 [1, -1] = true := by decide +kernel
theorem sub9_24 : sub9 [1, 0] = true := by decide +kernel
theorem sub9_25 : sub9 [1, 1] = true := by decide +kernel
theorem sub9_26 : sub9 [1, 2] = true := by decide +kernel
theorem sub9_27 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_28 : sub9 [2] = true := by decide +kernel
theorem sub9_29 : sub9 [3] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
