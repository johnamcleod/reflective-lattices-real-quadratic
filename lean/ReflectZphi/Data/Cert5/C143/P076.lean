import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd20_0_0 : subd20_0 [-3, -3] = true := by decide +kernel
theorem subd20_0_1 : subd20_0 [-3, -2] = true := by decide +kernel
theorem subd20_0_2 : subd20_0 [-3, -1] = true := by decide +kernel
theorem subd20_0_3 : subd20_0 [-3, 0] = true := by decide +kernel
theorem subd20_0_4 : subd20_0 [-3, 1] = true := by decide +kernel
theorem subd20_0_5 : subd20_0 [-3, 2] = true := by decide +kernel
theorem subd20_0_6 : subd20_0 [-2, -4] = true := by decide +kernel
theorem subd20_0_7 : subd20_0 [-2, -3] = true := by decide +kernel
theorem subd20_0_8 : subd20_0 [-2, -2] = true := by decide +kernel
theorem subd20_0_9 : subd20_0 [-2, -1] = true := by decide +kernel
theorem subd20_0_10 : subd20_0 [-2, 0] = true := by decide +kernel
theorem subd20_0_11 : subd20_0 [-2, 1] = true := by decide +kernel
theorem subd20_0_12 : subd20_0 [-2, 2] = true := by decide +kernel
theorem subd20_0_13 : subd20_0 [-2, 3] = true := by decide +kernel
theorem subd20_0_14 : subd20_0 [-1, -4] = true := by decide +kernel
theorem subd20_0_15 : subd20_0 [-1, -3] = true := by decide +kernel
theorem subd20_0_16 : subd20_0 [-1, -2] = true := by decide +kernel
theorem subd20_0_17 : subd20_0 [-1, -1] = true := by decide +kernel
theorem subd20_0_18 : subd20_0 [-1, 0] = true := by decide +kernel
theorem subd20_0_19 : subd20_0 [-1, 1] = true := by decide +kernel
theorem subd20_0_20 : subd20_0 [-1, 2] = true := by decide +kernel
theorem subd20_0_21 : subd20_0 [-1, 3] = true := by decide +kernel
theorem subd20_0_22 : subd20_0 [0, -4] = true := by decide +kernel
theorem subd20_0_23 : subd20_0 [0, -3] = true := by decide +kernel
theorem subd20_0_24 : subd20_0 [0, -2] = true := by decide +kernel
theorem subd20_0_25 : subd20_0 [0, -1] = true := by decide +kernel
theorem subd20_0_26 : subd20_0 [0, 0, -7] = true := by decide +kernel
theorem subd20_0_27 : subd20_0 [0, 0, -6] = true := by decide +kernel
theorem subd20_0_28 : subd20_0 [0, 0, -5] = true := by decide +kernel
theorem subd20_0_29 : subd20_0 [0, 0, -4] = true := by decide +kernel
theorem subd20_0_30 : subd20_0 [0, 0, -3] = true := by decide +kernel
theorem subd20_0_31 : subd20_0 [0, 0, -2] = true := by decide +kernel
theorem sbd20_0_0 : ∀ q ∈ blkd20_0_0, subd20_0 q = true := by
  unfold blkd20_0_0
  exact List.forall_mem_cons.2 ⟨subd20_0_0, List.forall_mem_cons.2 ⟨subd20_0_1, List.forall_mem_cons.2 ⟨subd20_0_2, List.forall_mem_cons.2 ⟨subd20_0_3, List.forall_mem_cons.2 ⟨subd20_0_4, List.forall_mem_cons.2 ⟨subd20_0_5, List.forall_mem_cons.2 ⟨subd20_0_6, List.forall_mem_cons.2 ⟨subd20_0_7, List.forall_mem_cons.2 ⟨subd20_0_8, List.forall_mem_cons.2 ⟨subd20_0_9, List.forall_mem_cons.2 ⟨subd20_0_10, List.forall_mem_cons.2 ⟨subd20_0_11, List.forall_mem_cons.2 ⟨subd20_0_12, List.forall_mem_cons.2 ⟨subd20_0_13, List.forall_mem_cons.2 ⟨subd20_0_14, List.forall_mem_cons.2 ⟨subd20_0_15, List.forall_mem_cons.2 ⟨subd20_0_16, List.forall_mem_cons.2 ⟨subd20_0_17, List.forall_mem_cons.2 ⟨subd20_0_18, List.forall_mem_cons.2 ⟨subd20_0_19, List.forall_mem_cons.2 ⟨subd20_0_20, List.forall_mem_cons.2 ⟨subd20_0_21, List.forall_mem_cons.2 ⟨subd20_0_22, List.forall_mem_cons.2 ⟨subd20_0_23, List.forall_mem_cons.2 ⟨subd20_0_24, List.forall_mem_cons.2 ⟨subd20_0_25, List.forall_mem_cons.2 ⟨subd20_0_26, List.forall_mem_cons.2 ⟨subd20_0_27, List.forall_mem_cons.2 ⟨subd20_0_28, List.forall_mem_cons.2 ⟨subd20_0_29, List.forall_mem_cons.2 ⟨subd20_0_30, List.forall_mem_cons.2 ⟨subd20_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_0_32 : subd20_0 [0, 0, -1] = true := by decide +kernel
theorem subd20_0_33 : subd20_0 [0, 0, 0] = true := by decide +kernel
theorem subd20_0_34 : subd20_0 [0, 0, 1] = true := by decide +kernel
theorem subd20_0_35 : subd20_0 [0, 0, 2] = true := by decide +kernel
theorem subd20_0_36 : subd20_0 [0, 0, 3] = true := by decide +kernel
theorem subd20_0_37 : subd20_0 [0, 0, 4] = true := by decide +kernel
theorem subd20_0_38 : subd20_0 [0, 0, 5] = true := by decide +kernel
theorem subd20_0_39 : subd20_0 [0, 0, 6] = true := by decide +kernel
theorem subd20_0_40 : subd20_0 [0, 1] = true := by decide +kernel
theorem subd20_0_41 : subd20_0 [0, 2] = true := by decide +kernel
theorem subd20_0_42 : subd20_0 [0, 3] = true := by decide +kernel
theorem subd20_0_43 : subd20_0 [1, -4] = true := by decide +kernel
theorem subd20_0_44 : subd20_0 [1, -3] = true := by decide +kernel
theorem subd20_0_45 : subd20_0 [1, -2] = true := by decide +kernel
theorem subd20_0_46 : subd20_0 [1, -1] = true := by decide +kernel
theorem subd20_0_47 : subd20_0 [1, 0] = true := by decide +kernel
theorem subd20_0_48 : subd20_0 [1, 1] = true := by decide +kernel
theorem subd20_0_49 : subd20_0 [1, 2] = true := by decide +kernel
theorem subd20_0_50 : subd20_0 [1, 3] = true := by decide +kernel
theorem subd20_0_51 : subd20_0 [2, -4] = true := by decide +kernel
theorem subd20_0_52 : subd20_0 [2, -3] = true := by decide +kernel
theorem subd20_0_53 : subd20_0 [2, -2] = true := by decide +kernel
theorem subd20_0_54 : subd20_0 [2, -1] = true := by decide +kernel
theorem subd20_0_55 : subd20_0 [2, 0] = true := by decide +kernel
theorem subd20_0_56 : subd20_0 [2, 1] = true := by decide +kernel
theorem subd20_0_57 : subd20_0 [2, 2] = true := by decide +kernel
theorem subd20_0_58 : subd20_0 [2, 3] = true := by decide +kernel
theorem subd20_0_59 : subd20_0 [3, -3] = true := by decide +kernel
theorem subd20_0_60 : subd20_0 [3, -2] = true := by decide +kernel
theorem subd20_0_61 : subd20_0 [3, -1] = true := by decide +kernel
theorem subd20_0_62 : subd20_0 [3, 0] = true := by decide +kernel
theorem subd20_0_63 : subd20_0 [3, 1] = true := by decide +kernel
theorem sbd20_0_1 : ∀ q ∈ blkd20_0_1, subd20_0 q = true := by
  unfold blkd20_0_1
  exact List.forall_mem_cons.2 ⟨subd20_0_32, List.forall_mem_cons.2 ⟨subd20_0_33, List.forall_mem_cons.2 ⟨subd20_0_34, List.forall_mem_cons.2 ⟨subd20_0_35, List.forall_mem_cons.2 ⟨subd20_0_36, List.forall_mem_cons.2 ⟨subd20_0_37, List.forall_mem_cons.2 ⟨subd20_0_38, List.forall_mem_cons.2 ⟨subd20_0_39, List.forall_mem_cons.2 ⟨subd20_0_40, List.forall_mem_cons.2 ⟨subd20_0_41, List.forall_mem_cons.2 ⟨subd20_0_42, List.forall_mem_cons.2 ⟨subd20_0_43, List.forall_mem_cons.2 ⟨subd20_0_44, List.forall_mem_cons.2 ⟨subd20_0_45, List.forall_mem_cons.2 ⟨subd20_0_46, List.forall_mem_cons.2 ⟨subd20_0_47, List.forall_mem_cons.2 ⟨subd20_0_48, List.forall_mem_cons.2 ⟨subd20_0_49, List.forall_mem_cons.2 ⟨subd20_0_50, List.forall_mem_cons.2 ⟨subd20_0_51, List.forall_mem_cons.2 ⟨subd20_0_52, List.forall_mem_cons.2 ⟨subd20_0_53, List.forall_mem_cons.2 ⟨subd20_0_54, List.forall_mem_cons.2 ⟨subd20_0_55, List.forall_mem_cons.2 ⟨subd20_0_56, List.forall_mem_cons.2 ⟨subd20_0_57, List.forall_mem_cons.2 ⟨subd20_0_58, List.forall_mem_cons.2 ⟨subd20_0_59, List.forall_mem_cons.2 ⟨subd20_0_60, List.forall_mem_cons.2 ⟨subd20_0_61, List.forall_mem_cons.2 ⟨subd20_0_62, List.forall_mem_cons.2 ⟨subd20_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_0_64 : subd20_0 [3, 2] = true := by decide +kernel
theorem sbd20_0_2 : ∀ q ∈ blkd20_0_2, subd20_0 q = true := by
  unfold blkd20_0_2
  exact List.forall_mem_cons.2 ⟨subd20_0_64, List.forall_mem_nil _⟩
theorem ld_okd20_1 : ldCheck G d20_1.U d20_1.ms ldd20_1 = true := by decide +kernel
theorem pre_okd20_1 : subPre G cell20 d20_1 = true := by decide +kernel
theorem subd20_1_0 : subd20_1 [-4, -3] = true := by decide +kernel
theorem subd20_1_1 : subd20_1 [-4, -2] = true := by decide +kernel
theorem subd20_1_2 : subd20_1 [-4, -1] = true := by decide +kernel
theorem subd20_1_3 : subd20_1 [-4, 0] = true := by decide +kernel
theorem subd20_1_4 : subd20_1 [-4, 1] = true := by decide +kernel
theorem subd20_1_5 : subd20_1 [-4, 2] = true := by decide +kernel
theorem subd20_1_6 : subd20_1 [-3, -4] = true := by decide +kernel
theorem subd20_1_7 : subd20_1 [-3, -3] = true := by decide +kernel
theorem subd20_1_8 : subd20_1 [-3, -2] = true := by decide +kernel
theorem subd20_1_9 : subd20_1 [-3, -1] = true := by decide +kernel
theorem subd20_1_10 : subd20_1 [-3, 0] = true := by decide +kernel
theorem subd20_1_11 : subd20_1 [-3, 1] = true := by decide +kernel
theorem subd20_1_12 : subd20_1 [-3, 2] = true := by decide +kernel
theorem subd20_1_13 : subd20_1 [-3, 3] = true := by decide +kernel
theorem subd20_1_14 : subd20_1 [-2, -5] = true := by decide +kernel
theorem subd20_1_15 : subd20_1 [-2, -4] = true := by decide +kernel
theorem subd20_1_16 : subd20_1 [-2, -3] = true := by decide +kernel
theorem subd20_1_17 : subd20_1 [-2, -2] = true := by decide +kernel
theorem subd20_1_18 : subd20_1 [-2, -1] = true := by decide +kernel
theorem subd20_1_19 : subd20_1 [-2, 0] = true := by decide +kernel
theorem subd20_1_20 : subd20_1 [-2, 1] = true := by decide +kernel
theorem subd20_1_21 : subd20_1 [-2, 2] = true := by decide +kernel
theorem subd20_1_22 : subd20_1 [-2, 3] = true := by decide +kernel
theorem subd20_1_23 : subd20_1 [-2, 4] = true := by decide +kernel
theorem subd20_1_24 : subd20_1 [-1, -5] = true := by decide +kernel
theorem subd20_1_25 : subd20_1 [-1, -4] = true := by decide +kernel
theorem subd20_1_26 : subd20_1 [-1, -3] = true := by decide +kernel
theorem subd20_1_27 : subd20_1 [-1, -2] = true := by decide +kernel
theorem subd20_1_28 : subd20_1 [-1, -1] = true := by decide +kernel
theorem subd20_1_29 : subd20_1 [-1, 0] = true := by decide +kernel
theorem subd20_1_30 : subd20_1 [-1, 1] = true := by decide +kernel
theorem subd20_1_31 : subd20_1 [-1, 2] = true := by decide +kernel
theorem sbd20_1_0 : ∀ q ∈ blkd20_1_0, subd20_1 q = true := by
  unfold blkd20_1_0
  exact List.forall_mem_cons.2 ⟨subd20_1_0, List.forall_mem_cons.2 ⟨subd20_1_1, List.forall_mem_cons.2 ⟨subd20_1_2, List.forall_mem_cons.2 ⟨subd20_1_3, List.forall_mem_cons.2 ⟨subd20_1_4, List.forall_mem_cons.2 ⟨subd20_1_5, List.forall_mem_cons.2 ⟨subd20_1_6, List.forall_mem_cons.2 ⟨subd20_1_7, List.forall_mem_cons.2 ⟨subd20_1_8, List.forall_mem_cons.2 ⟨subd20_1_9, List.forall_mem_cons.2 ⟨subd20_1_10, List.forall_mem_cons.2 ⟨subd20_1_11, List.forall_mem_cons.2 ⟨subd20_1_12, List.forall_mem_cons.2 ⟨subd20_1_13, List.forall_mem_cons.2 ⟨subd20_1_14, List.forall_mem_cons.2 ⟨subd20_1_15, List.forall_mem_cons.2 ⟨subd20_1_16, List.forall_mem_cons.2 ⟨subd20_1_17, List.forall_mem_cons.2 ⟨subd20_1_18, List.forall_mem_cons.2 ⟨subd20_1_19, List.forall_mem_cons.2 ⟨subd20_1_20, List.forall_mem_cons.2 ⟨subd20_1_21, List.forall_mem_cons.2 ⟨subd20_1_22, List.forall_mem_cons.2 ⟨subd20_1_23, List.forall_mem_cons.2 ⟨subd20_1_24, List.forall_mem_cons.2 ⟨subd20_1_25, List.forall_mem_cons.2 ⟨subd20_1_26, List.forall_mem_cons.2 ⟨subd20_1_27, List.forall_mem_cons.2 ⟨subd20_1_28, List.forall_mem_cons.2 ⟨subd20_1_29, List.forall_mem_cons.2 ⟨subd20_1_30, List.forall_mem_cons.2 ⟨subd20_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
