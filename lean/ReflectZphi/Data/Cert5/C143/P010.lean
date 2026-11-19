import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_3_0 : subd11_3 [-3] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-2, -4] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-1, -4] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-1, 3] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [0, -4] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [0, 0, -7] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [0, 0, -6] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [0, 0, -5] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [0, 0, -4] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [0, 0, -3] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [0, 0, -2] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [0, 0, -1] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [0, 0, 0] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [0, 0, 1] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [0, 0, 2] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [0, 0, 3] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [0, 0, 4] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [0, 0, 5] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [0, 0, 6] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [0, 3] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [1, -4] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_40 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_41 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_42 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_43 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_44 : subd11_3 [1, 3] = true := by decide +kernel
theorem subd11_3_45 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_46 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_47 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_48 : subd11_3 [2, 0] = true := by decide +kernel
theorem subd11_3_49 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_50 : subd11_3 [2, 2] = true := by decide +kernel
theorem subd11_3_51 : subd11_3 [2, 3] = true := by decide +kernel
theorem subd11_3_52 : subd11_3 [3] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_cons.2 ⟨subd11_3_40, List.forall_mem_cons.2 ⟨subd11_3_41, List.forall_mem_cons.2 ⟨subd11_3_42, List.forall_mem_cons.2 ⟨subd11_3_43, List.forall_mem_cons.2 ⟨subd11_3_44, List.forall_mem_cons.2 ⟨subd11_3_45, List.forall_mem_cons.2 ⟨subd11_3_46, List.forall_mem_cons.2 ⟨subd11_3_47, List.forall_mem_cons.2 ⟨subd11_3_48, List.forall_mem_cons.2 ⟨subd11_3_49, List.forall_mem_cons.2 ⟨subd11_3_50, List.forall_mem_cons.2 ⟨subd11_3_51, List.forall_mem_cons.2 ⟨subd11_3_52, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-5] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-4, -4] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-4, -3] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-4, -2] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-4, -1] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-4, 0] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-4, 1] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-4, 2] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-4, 3] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-3, -5] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [-3, -4] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [-3, -3] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [-3, -2] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [-3, -1] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [-3, 0] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [-3, 1] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [-3, 2] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [-3, 3] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [-3, 4] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [-2, -6] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [-2, -5] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [-2, -4] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [-2, -3] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [-2, -2] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [-2, -1] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [-2, 0] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [-2, 1] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [-2, 2] = true := by decide +kernel
theorem subd12_0_28 : subd12_0 [-2, 3] = true := by decide +kernel
theorem subd12_0_29 : subd12_0 [-2, 4] = true := by decide +kernel
theorem subd12_0_30 : subd12_0 [-1, -6] = true := by decide +kernel
theorem subd12_0_31 : subd12_0 [-1, -5] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_cons.2 ⟨subd12_0_28, List.forall_mem_cons.2 ⟨subd12_0_29, List.forall_mem_cons.2 ⟨subd12_0_30, List.forall_mem_cons.2 ⟨subd12_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
