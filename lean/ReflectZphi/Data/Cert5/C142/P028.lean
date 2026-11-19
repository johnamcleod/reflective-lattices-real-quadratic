import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_0_0 : subd15_0 [-4] = true := by decide +kernel
theorem subd15_0_1 : subd15_0 [-3] = true := by decide +kernel
theorem subd15_0_2 : subd15_0 [-2, -3] = true := by decide +kernel
theorem subd15_0_3 : subd15_0 [-2, -2] = true := by decide +kernel
theorem subd15_0_4 : subd15_0 [-2, -1] = true := by decide +kernel
theorem subd15_0_5 : subd15_0 [-2, 0] = true := by decide +kernel
theorem subd15_0_6 : subd15_0 [-2, 1] = true := by decide +kernel
theorem subd15_0_7 : subd15_0 [-2, 2] = true := by decide +kernel
theorem subd15_0_8 : subd15_0 [-2, 3] = true := by decide +kernel
theorem subd15_0_9 : subd15_0 [-1, -4] = true := by decide +kernel
theorem subd15_0_10 : subd15_0 [-1, -3] = true := by decide +kernel
theorem subd15_0_11 : subd15_0 [-1, -2] = true := by decide +kernel
theorem subd15_0_12 : subd15_0 [-1, -1] = true := by decide +kernel
theorem subd15_0_13 : subd15_0 [-1, 0] = true := by decide +kernel
theorem subd15_0_14 : subd15_0 [-1, 1] = true := by decide +kernel
theorem subd15_0_15 : subd15_0 [-1, 2] = true := by decide +kernel
theorem subd15_0_16 : subd15_0 [-1, 3] = true := by decide +kernel
theorem subd15_0_17 : subd15_0 [-1, 4] = true := by decide +kernel
theorem subd15_0_18 : subd15_0 [0, -4] = true := by decide +kernel
theorem subd15_0_19 : subd15_0 [0, -3] = true := by decide +kernel
theorem subd15_0_20 : subd15_0 [0, -2] = true := by decide +kernel
theorem subd15_0_21 : subd15_0 [0, -1] = true := by decide +kernel
theorem subd15_0_22 : subd15_0 [0, 0] = true := by decide +kernel
theorem subd15_0_23 : subd15_0 [0, 1] = true := by decide +kernel
theorem subd15_0_24 : subd15_0 [0, 2] = true := by decide +kernel
theorem subd15_0_25 : subd15_0 [0, 3] = true := by decide +kernel
theorem subd15_0_26 : subd15_0 [1, -5] = true := by decide +kernel
theorem subd15_0_27 : subd15_0 [1, -4] = true := by decide +kernel
theorem subd15_0_28 : subd15_0 [1, -3] = true := by decide +kernel
theorem subd15_0_29 : subd15_0 [1, -2] = true := by decide +kernel
theorem subd15_0_30 : subd15_0 [1, -1] = true := by decide +kernel
theorem subd15_0_31 : subd15_0 [1, 0] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_cons.2 ⟨subd15_0_1, List.forall_mem_cons.2 ⟨subd15_0_2, List.forall_mem_cons.2 ⟨subd15_0_3, List.forall_mem_cons.2 ⟨subd15_0_4, List.forall_mem_cons.2 ⟨subd15_0_5, List.forall_mem_cons.2 ⟨subd15_0_6, List.forall_mem_cons.2 ⟨subd15_0_7, List.forall_mem_cons.2 ⟨subd15_0_8, List.forall_mem_cons.2 ⟨subd15_0_9, List.forall_mem_cons.2 ⟨subd15_0_10, List.forall_mem_cons.2 ⟨subd15_0_11, List.forall_mem_cons.2 ⟨subd15_0_12, List.forall_mem_cons.2 ⟨subd15_0_13, List.forall_mem_cons.2 ⟨subd15_0_14, List.forall_mem_cons.2 ⟨subd15_0_15, List.forall_mem_cons.2 ⟨subd15_0_16, List.forall_mem_cons.2 ⟨subd15_0_17, List.forall_mem_cons.2 ⟨subd15_0_18, List.forall_mem_cons.2 ⟨subd15_0_19, List.forall_mem_cons.2 ⟨subd15_0_20, List.forall_mem_cons.2 ⟨subd15_0_21, List.forall_mem_cons.2 ⟨subd15_0_22, List.forall_mem_cons.2 ⟨subd15_0_23, List.forall_mem_cons.2 ⟨subd15_0_24, List.forall_mem_cons.2 ⟨subd15_0_25, List.forall_mem_cons.2 ⟨subd15_0_26, List.forall_mem_cons.2 ⟨subd15_0_27, List.forall_mem_cons.2 ⟨subd15_0_28, List.forall_mem_cons.2 ⟨subd15_0_29, List.forall_mem_cons.2 ⟨subd15_0_30, List.forall_mem_cons.2 ⟨subd15_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_0_32 : subd15_0 [1, 1] = true := by decide +kernel
theorem subd15_0_33 : subd15_0 [1, 2] = true := by decide +kernel
theorem subd15_0_34 : subd15_0 [1, 3] = true := by decide +kernel
theorem subd15_0_35 : subd15_0 [2, -4] = true := by decide +kernel
theorem subd15_0_36 : subd15_0 [2, -3] = true := by decide +kernel
theorem subd15_0_37 : subd15_0 [2, -2] = true := by decide +kernel
theorem subd15_0_38 : subd15_0 [2, -1] = true := by decide +kernel
theorem subd15_0_39 : subd15_0 [2, 0] = true := by decide +kernel
theorem subd15_0_40 : subd15_0 [2, 1] = true := by decide +kernel
theorem subd15_0_41 : subd15_0 [2, 2] = true := by decide +kernel
theorem subd15_0_42 : subd15_0 [3] = true := by decide +kernel
theorem subd15_0_43 : subd15_0 [4] = true := by decide +kernel
theorem sbd15_0_1 : ∀ q ∈ blkd15_0_1, subd15_0 q = true := by
  unfold blkd15_0_1
  exact List.forall_mem_cons.2 ⟨subd15_0_32, List.forall_mem_cons.2 ⟨subd15_0_33, List.forall_mem_cons.2 ⟨subd15_0_34, List.forall_mem_cons.2 ⟨subd15_0_35, List.forall_mem_cons.2 ⟨subd15_0_36, List.forall_mem_cons.2 ⟨subd15_0_37, List.forall_mem_cons.2 ⟨subd15_0_38, List.forall_mem_cons.2 ⟨subd15_0_39, List.forall_mem_cons.2 ⟨subd15_0_40, List.forall_mem_cons.2 ⟨subd15_0_41, List.forall_mem_cons.2 ⟨subd15_0_42, List.forall_mem_cons.2 ⟨subd15_0_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [-3] = true := by decide +kernel
theorem subd15_1_1 : subd15_1 [-2, -3] = true := by decide +kernel
theorem subd15_1_2 : subd15_1 [-2, -2] = true := by decide +kernel
theorem subd15_1_3 : subd15_1 [-2, -1] = true := by decide +kernel
theorem subd15_1_4 : subd15_1 [-2, 0] = true := by decide +kernel
theorem subd15_1_5 : subd15_1 [-2, 1] = true := by decide +kernel
theorem subd15_1_6 : subd15_1 [-2, 2] = true := by decide +kernel
theorem subd15_1_7 : subd15_1 [-1, -4] = true := by decide +kernel
theorem subd15_1_8 : subd15_1 [-1, -3] = true := by decide +kernel
theorem subd15_1_9 : subd15_1 [-1, -2] = true := by decide +kernel
theorem subd15_1_10 : subd15_1 [-1, -1] = true := by decide +kernel
theorem subd15_1_11 : subd15_1 [-1, 0] = true := by decide +kernel
theorem subd15_1_12 : subd15_1 [-1, 1] = true := by decide +kernel
theorem subd15_1_13 : subd15_1 [-1, 2] = true := by decide +kernel
theorem subd15_1_14 : subd15_1 [-1, 3] = true := by decide +kernel
theorem subd15_1_15 : subd15_1 [0, -4] = true := by decide +kernel
theorem subd15_1_16 : subd15_1 [0, -3] = true := by decide +kernel
theorem subd15_1_17 : subd15_1 [0, -2] = true := by decide +kernel
theorem subd15_1_18 : subd15_1 [0, -1] = true := by decide +kernel
theorem subd15_1_19 : subd15_1 [0, 0] = true := by decide +kernel
theorem subd15_1_20 : subd15_1 [0, 1] = true := by decide +kernel
theorem subd15_1_21 : subd15_1 [0, 2] = true := by decide +kernel
theorem subd15_1_22 : subd15_1 [0, 3] = true := by decide +kernel
theorem subd15_1_23 : subd15_1 [1, -4] = true := by decide +kernel
theorem subd15_1_24 : subd15_1 [1, -3] = true := by decide +kernel
theorem subd15_1_25 : subd15_1 [1, -2] = true := by decide +kernel
theorem subd15_1_26 : subd15_1 [1, -1] = true := by decide +kernel
theorem subd15_1_27 : subd15_1 [1, 0] = true := by decide +kernel
theorem subd15_1_28 : subd15_1 [1, 1] = true := by decide +kernel
theorem subd15_1_29 : subd15_1 [1, 2] = true := by decide +kernel
theorem subd15_1_30 : subd15_1 [1, 3] = true := by decide +kernel
theorem subd15_1_31 : subd15_1 [2, -3] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_cons.2 ⟨subd15_1_1, List.forall_mem_cons.2 ⟨subd15_1_2, List.forall_mem_cons.2 ⟨subd15_1_3, List.forall_mem_cons.2 ⟨subd15_1_4, List.forall_mem_cons.2 ⟨subd15_1_5, List.forall_mem_cons.2 ⟨subd15_1_6, List.forall_mem_cons.2 ⟨subd15_1_7, List.forall_mem_cons.2 ⟨subd15_1_8, List.forall_mem_cons.2 ⟨subd15_1_9, List.forall_mem_cons.2 ⟨subd15_1_10, List.forall_mem_cons.2 ⟨subd15_1_11, List.forall_mem_cons.2 ⟨subd15_1_12, List.forall_mem_cons.2 ⟨subd15_1_13, List.forall_mem_cons.2 ⟨subd15_1_14, List.forall_mem_cons.2 ⟨subd15_1_15, List.forall_mem_cons.2 ⟨subd15_1_16, List.forall_mem_cons.2 ⟨subd15_1_17, List.forall_mem_cons.2 ⟨subd15_1_18, List.forall_mem_cons.2 ⟨subd15_1_19, List.forall_mem_cons.2 ⟨subd15_1_20, List.forall_mem_cons.2 ⟨subd15_1_21, List.forall_mem_cons.2 ⟨subd15_1_22, List.forall_mem_cons.2 ⟨subd15_1_23, List.forall_mem_cons.2 ⟨subd15_1_24, List.forall_mem_cons.2 ⟨subd15_1_25, List.forall_mem_cons.2 ⟨subd15_1_26, List.forall_mem_cons.2 ⟨subd15_1_27, List.forall_mem_cons.2 ⟨subd15_1_28, List.forall_mem_cons.2 ⟨subd15_1_29, List.forall_mem_cons.2 ⟨subd15_1_30, List.forall_mem_cons.2 ⟨subd15_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_1_32 : subd15_1 [2, -2] = true := by decide +kernel
theorem subd15_1_33 : subd15_1 [2, -1] = true := by decide +kernel
theorem subd15_1_34 : subd15_1 [2, 0] = true := by decide +kernel
theorem subd15_1_35 : subd15_1 [2, 1] = true := by decide +kernel
theorem subd15_1_36 : subd15_1 [2, 2] = true := by decide +kernel
theorem subd15_1_37 : subd15_1 [3] = true := by decide +kernel
theorem sbd15_1_1 : ∀ q ∈ blkd15_1_1, subd15_1 q = true := by
  unfold blkd15_1_1
  exact List.forall_mem_cons.2 ⟨subd15_1_32, List.forall_mem_cons.2 ⟨subd15_1_33, List.forall_mem_cons.2 ⟨subd15_1_34, List.forall_mem_cons.2 ⟨subd15_1_35, List.forall_mem_cons.2 ⟨subd15_1_36, List.forall_mem_cons.2 ⟨subd15_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [-5, -7] = true := by decide +kernel
theorem subd15_2_1 : subd15_2 [-5, -6] = true := by decide +kernel
theorem subd15_2_2 : subd15_2 [-5, -5] = true := by decide +kernel
theorem subd15_2_3 : subd15_2 [-5, -4] = true := by decide +kernel
theorem subd15_2_4 : subd15_2 [-5, -3] = true := by decide +kernel
theorem subd15_2_5 : subd15_2 [-5, -2] = true := by decide +kernel
theorem subd15_2_6 : subd15_2 [-5, -1] = true := by decide +kernel
theorem subd15_2_7 : subd15_2 [-5, 0] = true := by decide +kernel
theorem subd15_2_8 : subd15_2 [-5, 1] = true := by decide +kernel
theorem subd15_2_9 : subd15_2 [-4, -7] = true := by decide +kernel
theorem subd15_2_10 : subd15_2 [-4, -6] = true := by decide +kernel
theorem subd15_2_11 : subd15_2 [-4, -5] = true := by decide +kernel
theorem subd15_2_12 : subd15_2 [-4, -4] = true := by decide +kernel
theorem subd15_2_13 : subd15_2 [-4, -3, -8] = true := by decide +kernel
theorem subd15_2_14 : subd15_2 [-4, -3, -7] = true := by decide +kernel
theorem subd15_2_15 : subd15_2 [-4, -3, -6] = true := by decide +kernel
theorem subd15_2_16 : subd15_2 [-4, -3, -5] = true := by decide +kernel
theorem subd15_2_17 : subd15_2 [-4, -3, -4] = true := by decide +kernel
theorem subd15_2_18 : subd15_2 [-4, -3, -3] = true := by decide +kernel
theorem subd15_2_19 : subd15_2 [-4, -3, -2] = true := by decide +kernel
theorem subd15_2_20 : subd15_2 [-4, -3, -1] = true := by decide +kernel
theorem subd15_2_21 : subd15_2 [-4, -3, 0] = true := by decide +kernel
theorem subd15_2_22 : subd15_2 [-4, -3, 1] = true := by decide +kernel
theorem subd15_2_23 : subd15_2 [-4, -3, 2] = true := by decide +kernel
theorem subd15_2_24 : subd15_2 [-4, -3, 3] = true := by decide +kernel
theorem subd15_2_25 : subd15_2 [-4, -3, 4] = true := by decide +kernel
theorem subd15_2_26 : subd15_2 [-4, -3, 5] = true := by decide +kernel
theorem subd15_2_27 : subd15_2 [-4, -2, -8] = true := by decide +kernel
theorem subd15_2_28 : subd15_2 [-4, -2, -7] = true := by decide +kernel
theorem subd15_2_29 : subd15_2 [-4, -2, -6] = true := by decide +kernel
theorem subd15_2_30 : subd15_2 [-4, -2, -5] = true := by decide +kernel
theorem subd15_2_31 : subd15_2 [-4, -2, -4] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_cons.2 ⟨subd15_2_1, List.forall_mem_cons.2 ⟨subd15_2_2, List.forall_mem_cons.2 ⟨subd15_2_3, List.forall_mem_cons.2 ⟨subd15_2_4, List.forall_mem_cons.2 ⟨subd15_2_5, List.forall_mem_cons.2 ⟨subd15_2_6, List.forall_mem_cons.2 ⟨subd15_2_7, List.forall_mem_cons.2 ⟨subd15_2_8, List.forall_mem_cons.2 ⟨subd15_2_9, List.forall_mem_cons.2 ⟨subd15_2_10, List.forall_mem_cons.2 ⟨subd15_2_11, List.forall_mem_cons.2 ⟨subd15_2_12, List.forall_mem_cons.2 ⟨subd15_2_13, List.forall_mem_cons.2 ⟨subd15_2_14, List.forall_mem_cons.2 ⟨subd15_2_15, List.forall_mem_cons.2 ⟨subd15_2_16, List.forall_mem_cons.2 ⟨subd15_2_17, List.forall_mem_cons.2 ⟨subd15_2_18, List.forall_mem_cons.2 ⟨subd15_2_19, List.forall_mem_cons.2 ⟨subd15_2_20, List.forall_mem_cons.2 ⟨subd15_2_21, List.forall_mem_cons.2 ⟨subd15_2_22, List.forall_mem_cons.2 ⟨subd15_2_23, List.forall_mem_cons.2 ⟨subd15_2_24, List.forall_mem_cons.2 ⟨subd15_2_25, List.forall_mem_cons.2 ⟨subd15_2_26, List.forall_mem_cons.2 ⟨subd15_2_27, List.forall_mem_cons.2 ⟨subd15_2_28, List.forall_mem_cons.2 ⟨subd15_2_29, List.forall_mem_cons.2 ⟨subd15_2_30, List.forall_mem_cons.2 ⟨subd15_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_32 : subd15_2 [-4, -2, -3] = true := by decide +kernel
theorem subd15_2_33 : subd15_2 [-4, -2, -2] = true := by decide +kernel
theorem subd15_2_34 : subd15_2 [-4, -2, -1] = true := by decide +kernel
theorem subd15_2_35 : subd15_2 [-4, -2, 0] = true := by decide +kernel
theorem subd15_2_36 : subd15_2 [-4, -2, 1] = true := by decide +kernel
theorem subd15_2_37 : subd15_2 [-4, -2, 2] = true := by decide +kernel
theorem subd15_2_38 : subd15_2 [-4, -2, 3] = true := by decide +kernel
theorem subd15_2_39 : subd15_2 [-4, -2, 4] = true := by decide +kernel
theorem subd15_2_40 : subd15_2 [-4, -2, 5] = true := by decide +kernel
theorem subd15_2_41 : subd15_2 [-4, -1, -8] = true := by decide +kernel
theorem subd15_2_42 : subd15_2 [-4, -1, -7] = true := by decide +kernel
theorem subd15_2_43 : subd15_2 [-4, -1, -6] = true := by decide +kernel
theorem subd15_2_44 : subd15_2 [-4, -1, -5] = true := by decide +kernel
theorem subd15_2_45 : subd15_2 [-4, -1, -4] = true := by decide +kernel
theorem subd15_2_46 : subd15_2 [-4, -1, -3] = true := by decide +kernel
theorem subd15_2_47 : subd15_2 [-4, -1, -2] = true := by decide +kernel
theorem subd15_2_48 : subd15_2 [-4, -1, -1] = true := by decide +kernel
theorem subd15_2_49 : subd15_2 [-4, -1, 0] = true := by decide +kernel
theorem subd15_2_50 : subd15_2 [-4, -1, 1] = true := by decide +kernel
theorem subd15_2_51 : subd15_2 [-4, -1, 2] = true := by decide +kernel
theorem subd15_2_52 : subd15_2 [-4, -1, 3] = true := by decide +kernel
theorem subd15_2_53 : subd15_2 [-4, -1, 4] = true := by decide +kernel
theorem subd15_2_54 : subd15_2 [-4, -1, 5] = true := by decide +kernel
theorem subd15_2_55 : subd15_2 [-4, 0] = true := by decide +kernel
theorem subd15_2_56 : subd15_2 [-4, 1] = true := by decide +kernel
theorem subd15_2_57 : subd15_2 [-4, 2] = true := by decide +kernel
theorem subd15_2_58 : subd15_2 [-4, 3] = true := by decide +kernel
theorem subd15_2_59 : subd15_2 [-3, -8] = true := by decide +kernel
theorem subd15_2_60 : subd15_2 [-3, -7] = true := by decide +kernel
theorem subd15_2_61 : subd15_2 [-3, -6] = true := by decide +kernel
theorem subd15_2_62 : subd15_2 [-3, -5] = true := by decide +kernel
theorem subd15_2_63 : subd15_2 [-3, -4, -8] = true := by decide +kernel
theorem sbd15_2_1 : ∀ q ∈ blkd15_2_1, subd15_2 q = true := by
  unfold blkd15_2_1
  exact List.forall_mem_cons.2 ⟨subd15_2_32, List.forall_mem_cons.2 ⟨subd15_2_33, List.forall_mem_cons.2 ⟨subd15_2_34, List.forall_mem_cons.2 ⟨subd15_2_35, List.forall_mem_cons.2 ⟨subd15_2_36, List.forall_mem_cons.2 ⟨subd15_2_37, List.forall_mem_cons.2 ⟨subd15_2_38, List.forall_mem_cons.2 ⟨subd15_2_39, List.forall_mem_cons.2 ⟨subd15_2_40, List.forall_mem_cons.2 ⟨subd15_2_41, List.forall_mem_cons.2 ⟨subd15_2_42, List.forall_mem_cons.2 ⟨subd15_2_43, List.forall_mem_cons.2 ⟨subd15_2_44, List.forall_mem_cons.2 ⟨subd15_2_45, List.forall_mem_cons.2 ⟨subd15_2_46, List.forall_mem_cons.2 ⟨subd15_2_47, List.forall_mem_cons.2 ⟨subd15_2_48, List.forall_mem_cons.2 ⟨subd15_2_49, List.forall_mem_cons.2 ⟨subd15_2_50, List.forall_mem_cons.2 ⟨subd15_2_51, List.forall_mem_cons.2 ⟨subd15_2_52, List.forall_mem_cons.2 ⟨subd15_2_53, List.forall_mem_cons.2 ⟨subd15_2_54, List.forall_mem_cons.2 ⟨subd15_2_55, List.forall_mem_cons.2 ⟨subd15_2_56, List.forall_mem_cons.2 ⟨subd15_2_57, List.forall_mem_cons.2 ⟨subd15_2_58, List.forall_mem_cons.2 ⟨subd15_2_59, List.forall_mem_cons.2 ⟨subd15_2_60, List.forall_mem_cons.2 ⟨subd15_2_61, List.forall_mem_cons.2 ⟨subd15_2_62, List.forall_mem_cons.2 ⟨subd15_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_64 : subd15_2 [-3, -4, -7] = true := by decide +kernel
theorem subd15_2_65 : subd15_2 [-3, -4, -6] = true := by decide +kernel
theorem subd15_2_66 : subd15_2 [-3, -4, -5] = true := by decide +kernel
theorem subd15_2_67 : subd15_2 [-3, -4, -4] = true := by decide +kernel
theorem subd15_2_68 : subd15_2 [-3, -4, -3] = true := by decide +kernel
theorem subd15_2_69 : subd15_2 [-3, -4, -2] = true := by decide +kernel
theorem subd15_2_70 : subd15_2 [-3, -4, -1] = true := by decide +kernel
theorem subd15_2_71 : subd15_2 [-3, -4, 0] = true := by decide +kernel
theorem subd15_2_72 : subd15_2 [-3, -4, 1] = true := by decide +kernel
theorem subd15_2_73 : subd15_2 [-3, -4, 2] = true := by decide +kernel
theorem subd15_2_74 : subd15_2 [-3, -4, 3] = true := by decide +kernel
theorem subd15_2_75 : subd15_2 [-3, -4, 4] = true := by decide +kernel
theorem subd15_2_76 : subd15_2 [-3, -4, 5] = true := by decide +kernel
theorem subd15_2_77 : subd15_2 [-3, -4, 6] = true := by decide +kernel
theorem subd15_2_78 : subd15_2 [-3, -3, -9] = true := by decide +kernel
theorem subd15_2_79 : subd15_2 [-3, -3, -8] = true := by decide +kernel
theorem subd15_2_80 : subd15_2 [-3, -3, -7] = true := by decide +kernel
theorem subd15_2_81 : subd15_2 [-3, -3, -6] = true := by decide +kernel
theorem subd15_2_82 : subd15_2 [-3, -3, -5] = true := by decide +kernel
theorem subd15_2_83 : subd15_2 [-3, -3, -4] = true := by decide +kernel
theorem subd15_2_84 : subd15_2 [-3, -3, -3] = true := by decide +kernel
theorem subd15_2_85 : subd15_2 [-3, -3, -2] = true := by decide +kernel
theorem subd15_2_86 : subd15_2 [-3, -3, -1] = true := by decide +kernel
theorem subd15_2_87 : subd15_2 [-3, -3, 0] = true := by decide +kernel
theorem subd15_2_88 : subd15_2 [-3, -3, 1] = true := by decide +kernel
theorem subd15_2_89 : subd15_2 [-3, -3, 2] = true := by decide +kernel
theorem subd15_2_90 : subd15_2 [-3, -3, 3] = true := by decide +kernel
theorem subd15_2_91 : subd15_2 [-3, -3, 4] = true := by decide +kernel
theorem subd15_2_92 : subd15_2 [-3, -3, 5] = true := by decide +kernel
theorem subd15_2_93 : subd15_2 [-3, -3, 6] = true := by decide +kernel
theorem subd15_2_94 : subd15_2 [-3, -2, -9] = true := by decide +kernel
theorem subd15_2_95 : subd15_2 [-3, -2, -8] = true := by decide +kernel
theorem sbd15_2_2 : ∀ q ∈ blkd15_2_2, subd15_2 q = true := by
  unfold blkd15_2_2
  exact List.forall_mem_cons.2 ⟨subd15_2_64, List.forall_mem_cons.2 ⟨subd15_2_65, List.forall_mem_cons.2 ⟨subd15_2_66, List.forall_mem_cons.2 ⟨subd15_2_67, List.forall_mem_cons.2 ⟨subd15_2_68, List.forall_mem_cons.2 ⟨subd15_2_69, List.forall_mem_cons.2 ⟨subd15_2_70, List.forall_mem_cons.2 ⟨subd15_2_71, List.forall_mem_cons.2 ⟨subd15_2_72, List.forall_mem_cons.2 ⟨subd15_2_73, List.forall_mem_cons.2 ⟨subd15_2_74, List.forall_mem_cons.2 ⟨subd15_2_75, List.forall_mem_cons.2 ⟨subd15_2_76, List.forall_mem_cons.2 ⟨subd15_2_77, List.forall_mem_cons.2 ⟨subd15_2_78, List.forall_mem_cons.2 ⟨subd15_2_79, List.forall_mem_cons.2 ⟨subd15_2_80, List.forall_mem_cons.2 ⟨subd15_2_81, List.forall_mem_cons.2 ⟨subd15_2_82, List.forall_mem_cons.2 ⟨subd15_2_83, List.forall_mem_cons.2 ⟨subd15_2_84, List.forall_mem_cons.2 ⟨subd15_2_85, List.forall_mem_cons.2 ⟨subd15_2_86, List.forall_mem_cons.2 ⟨subd15_2_87, List.forall_mem_cons.2 ⟨subd15_2_88, List.forall_mem_cons.2 ⟨subd15_2_89, List.forall_mem_cons.2 ⟨subd15_2_90, List.forall_mem_cons.2 ⟨subd15_2_91, List.forall_mem_cons.2 ⟨subd15_2_92, List.forall_mem_cons.2 ⟨subd15_2_93, List.forall_mem_cons.2 ⟨subd15_2_94, List.forall_mem_cons.2 ⟨subd15_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_96 : subd15_2 [-3, -2, -7] = true := by decide +kernel
theorem subd15_2_97 : subd15_2 [-3, -2, -6] = true := by decide +kernel
theorem subd15_2_98 : subd15_2 [-3, -2, -5] = true := by decide +kernel
theorem subd15_2_99 : subd15_2 [-3, -2, -4] = true := by decide +kernel
theorem subd15_2_100 : subd15_2 [-3, -2, -3] = true := by decide +kernel
theorem subd15_2_101 : subd15_2 [-3, -2, -2] = true := by decide +kernel
theorem subd15_2_102 : subd15_2 [-3, -2, -1] = true := by decide +kernel
theorem subd15_2_103 : subd15_2 [-3, -2, 0] = true := by decide +kernel
theorem subd15_2_104 : subd15_2 [-3, -2, 1] = true := by decide +kernel
theorem subd15_2_105 : subd15_2 [-3, -2, 2] = true := by decide +kernel
theorem subd15_2_106 : subd15_2 [-3, -2, 3] = true := by decide +kernel
theorem subd15_2_107 : subd15_2 [-3, -2, 4] = true := by decide +kernel
theorem subd15_2_108 : subd15_2 [-3, -2, 5] = true := by decide +kernel
theorem subd15_2_109 : subd15_2 [-3, -2, 6] = true := by decide +kernel
theorem subd15_2_110 : subd15_2 [-3, -1, -9] = true := by decide +kernel
theorem subd15_2_111 : subd15_2 [-3, -1, -8] = true := by decide +kernel
theorem subd15_2_112 : subd15_2 [-3, -1, -7] = true := by decide +kernel
theorem subd15_2_113 : subd15_2 [-3, -1, -6] = true := by decide +kernel
theorem subd15_2_114 : subd15_2 [-3, -1, -5] = true := by decide +kernel
theorem subd15_2_115 : subd15_2 [-3, -1, -4] = true := by decide +kernel
theorem subd15_2_116 : subd15_2 [-3, -1, -3] = true := by decide +kernel
theorem subd15_2_117 : subd15_2 [-3, -1, -2] = true := by decide +kernel
theorem subd15_2_118 : subd15_2 [-3, -1, -1] = true := by decide +kernel
theorem subd15_2_119 : subd15_2 [-3, -1, 0] = true := by decide +kernel
theorem subd15_2_120 : subd15_2 [-3, -1, 1] = true := by decide +kernel
theorem subd15_2_121 : subd15_2 [-3, -1, 2] = true := by decide +kernel
theorem subd15_2_122 : subd15_2 [-3, -1, 3] = true := by decide +kernel
theorem subd15_2_123 : subd15_2 [-3, -1, 4] = true := by decide +kernel
theorem subd15_2_124 : subd15_2 [-3, -1, 5] = true := by decide +kernel
theorem subd15_2_125 : subd15_2 [-3, -1, 6] = true := by decide +kernel
theorem subd15_2_126 : subd15_2 [-3, 0, -9] = true := by decide +kernel
theorem subd15_2_127 : subd15_2 [-3, 0, -8] = true := by decide +kernel
theorem sbd15_2_3 : ∀ q ∈ blkd15_2_3, subd15_2 q = true := by
  unfold blkd15_2_3
  exact List.forall_mem_cons.2 ⟨subd15_2_96, List.forall_mem_cons.2 ⟨subd15_2_97, List.forall_mem_cons.2 ⟨subd15_2_98, List.forall_mem_cons.2 ⟨subd15_2_99, List.forall_mem_cons.2 ⟨subd15_2_100, List.forall_mem_cons.2 ⟨subd15_2_101, List.forall_mem_cons.2 ⟨subd15_2_102, List.forall_mem_cons.2 ⟨subd15_2_103, List.forall_mem_cons.2 ⟨subd15_2_104, List.forall_mem_cons.2 ⟨subd15_2_105, List.forall_mem_cons.2 ⟨subd15_2_106, List.forall_mem_cons.2 ⟨subd15_2_107, List.forall_mem_cons.2 ⟨subd15_2_108, List.forall_mem_cons.2 ⟨subd15_2_109, List.forall_mem_cons.2 ⟨subd15_2_110, List.forall_mem_cons.2 ⟨subd15_2_111, List.forall_mem_cons.2 ⟨subd15_2_112, List.forall_mem_cons.2 ⟨subd15_2_113, List.forall_mem_cons.2 ⟨subd15_2_114, List.forall_mem_cons.2 ⟨subd15_2_115, List.forall_mem_cons.2 ⟨subd15_2_116, List.forall_mem_cons.2 ⟨subd15_2_117, List.forall_mem_cons.2 ⟨subd15_2_118, List.forall_mem_cons.2 ⟨subd15_2_119, List.forall_mem_cons.2 ⟨subd15_2_120, List.forall_mem_cons.2 ⟨subd15_2_121, List.forall_mem_cons.2 ⟨subd15_2_122, List.forall_mem_cons.2 ⟨subd15_2_123, List.forall_mem_cons.2 ⟨subd15_2_124, List.forall_mem_cons.2 ⟨subd15_2_125, List.forall_mem_cons.2 ⟨subd15_2_126, List.forall_mem_cons.2 ⟨subd15_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
