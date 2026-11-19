import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_32 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [0, 4] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [1, -5] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [1, 4] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [1, 5] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [2, -4] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [2, -3] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [2, 0] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [2, 3] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [2, 4] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [2, 5] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [3, -3] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [3, -2] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [3, -1] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [3, 0] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [3, 1] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [3, 2] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [3, 3] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [3, 4] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [4] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-4] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [2] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [3] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [4] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-1, -2, -9] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-1, -2, -8] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-1, -2, -7] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-1, -2, -6] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-1, -2, -5] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-1, -2, -4] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-1, -2, -3] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-1, -2, -2] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-1, -2, -1] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-1, -2, 0] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-1, -2, 1] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [-1, -2, 2] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [-1, -2, 3] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [-1, -2, 4] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [-1, -2, 5] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [-1, -1, -9] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [-1, -1, -8] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [-1, -1, -7] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [-1, -1, -6] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [-1, -1, -5] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [-1, -1, -4] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [-1, -1, -3] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [-1, -1, -2] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [-1, -1, -1] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [-1, -1, 0] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [-1, -1, 1] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [-1, -1, 2] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [-1, -1, 3] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [-1, -1, 4] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [-1, -1, 5] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [-1, -1, 6] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [-1, -1, 7] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [-1, 0, -9] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [-1, 0, -8] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [-1, 0, -7] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [-1, 0, -6] = true := by decide +kernel
theorem subd11_2_42 : subd11_2 [-1, 0, -5] = true := by decide +kernel
theorem subd11_2_43 : subd11_2 [-1, 0, -4] = true := by decide +kernel
theorem subd11_2_44 : subd11_2 [-1, 0, -3] = true := by decide +kernel
theorem subd11_2_45 : subd11_2 [-1, 0, -2] = true := by decide +kernel
theorem subd11_2_46 : subd11_2 [-1, 0, -1] = true := by decide +kernel
theorem subd11_2_47 : subd11_2 [-1, 0, 0] = true := by decide +kernel
theorem subd11_2_48 : subd11_2 [-1, 0, 1] = true := by decide +kernel
theorem subd11_2_49 : subd11_2 [-1, 0, 2] = true := by decide +kernel
theorem subd11_2_50 : subd11_2 [-1, 0, 3] = true := by decide +kernel
theorem subd11_2_51 : subd11_2 [-1, 0, 4] = true := by decide +kernel
theorem subd11_2_52 : subd11_2 [-1, 0, 5] = true := by decide +kernel
theorem subd11_2_53 : subd11_2 [-1, 0, 6] = true := by decide +kernel
theorem subd11_2_54 : subd11_2 [-1, 0, 7] = true := by decide +kernel
theorem subd11_2_55 : subd11_2 [-1, 1, -8] = true := by decide +kernel
theorem subd11_2_56 : subd11_2 [-1, 1, -7] = true := by decide +kernel
theorem subd11_2_57 : subd11_2 [-1, 1, -6] = true := by decide +kernel
theorem subd11_2_58 : subd11_2 [-1, 1, -5] = true := by decide +kernel
theorem subd11_2_59 : subd11_2 [-1, 1, -4] = true := by decide +kernel
theorem subd11_2_60 : subd11_2 [-1, 1, -3] = true := by decide +kernel
theorem subd11_2_61 : subd11_2 [-1, 1, -2] = true := by decide +kernel
theorem subd11_2_62 : subd11_2 [-1, 1, -1] = true := by decide +kernel
theorem subd11_2_63 : subd11_2 [-1, 1, 0] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_cons.2 ⟨subd11_2_42, List.forall_mem_cons.2 ⟨subd11_2_43, List.forall_mem_cons.2 ⟨subd11_2_44, List.forall_mem_cons.2 ⟨subd11_2_45, List.forall_mem_cons.2 ⟨subd11_2_46, List.forall_mem_cons.2 ⟨subd11_2_47, List.forall_mem_cons.2 ⟨subd11_2_48, List.forall_mem_cons.2 ⟨subd11_2_49, List.forall_mem_cons.2 ⟨subd11_2_50, List.forall_mem_cons.2 ⟨subd11_2_51, List.forall_mem_cons.2 ⟨subd11_2_52, List.forall_mem_cons.2 ⟨subd11_2_53, List.forall_mem_cons.2 ⟨subd11_2_54, List.forall_mem_cons.2 ⟨subd11_2_55, List.forall_mem_cons.2 ⟨subd11_2_56, List.forall_mem_cons.2 ⟨subd11_2_57, List.forall_mem_cons.2 ⟨subd11_2_58, List.forall_mem_cons.2 ⟨subd11_2_59, List.forall_mem_cons.2 ⟨subd11_2_60, List.forall_mem_cons.2 ⟨subd11_2_61, List.forall_mem_cons.2 ⟨subd11_2_62, List.forall_mem_cons.2 ⟨subd11_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_64 : subd11_2 [-1, 1, 1] = true := by decide +kernel
theorem subd11_2_65 : subd11_2 [-1, 1, 2] = true := by decide +kernel
theorem subd11_2_66 : subd11_2 [-1, 1, 3] = true := by decide +kernel
theorem subd11_2_67 : subd11_2 [-1, 1, 4] = true := by decide +kernel
theorem subd11_2_68 : subd11_2 [-1, 1, 5] = true := by decide +kernel
theorem subd11_2_69 : subd11_2 [-1, 1, 6] = true := by decide +kernel
theorem subd11_2_70 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_71 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_72 : subd11_2 [0, -2, -8] = true := by decide +kernel
theorem subd11_2_73 : subd11_2 [0, -2, -7] = true := by decide +kernel
theorem subd11_2_74 : subd11_2 [0, -2, -6] = true := by decide +kernel
theorem subd11_2_75 : subd11_2 [0, -2, -5] = true := by decide +kernel
theorem subd11_2_76 : subd11_2 [0, -2, -4] = true := by decide +kernel
theorem subd11_2_77 : subd11_2 [0, -2, -3] = true := by decide +kernel
theorem subd11_2_78 : subd11_2 [0, -2, -2] = true := by decide +kernel
theorem subd11_2_79 : subd11_2 [0, -2, -1] = true := by decide +kernel
theorem subd11_2_80 : subd11_2 [0, -2, 0] = true := by decide +kernel
theorem subd11_2_81 : subd11_2 [0, -2, 1] = true := by decide +kernel
theorem subd11_2_82 : subd11_2 [0, -2, 2] = true := by decide +kernel
theorem subd11_2_83 : subd11_2 [0, -2, 3] = true := by decide +kernel
theorem subd11_2_84 : subd11_2 [0, -2, 4] = true := by decide +kernel
theorem subd11_2_85 : subd11_2 [0, -2, 5] = true := by decide +kernel
theorem subd11_2_86 : subd11_2 [0, -1, -9] = true := by decide +kernel
theorem subd11_2_87 : subd11_2 [0, -1, -8] = true := by decide +kernel
theorem subd11_2_88 : subd11_2 [0, -1, -7] = true := by decide +kernel
theorem subd11_2_89 : subd11_2 [0, -1, -6] = true := by decide +kernel
theorem subd11_2_90 : subd11_2 [0, -1, -5] = true := by decide +kernel
theorem subd11_2_91 : subd11_2 [0, -1, -4] = true := by decide +kernel
theorem subd11_2_92 : subd11_2 [0, -1, -3] = true := by decide +kernel
theorem subd11_2_93 : subd11_2 [0, -1, -2] = true := by decide +kernel
theorem subd11_2_94 : subd11_2 [0, -1, -1] = true := by decide +kernel
theorem subd11_2_95 : subd11_2 [0, -1, 0] = true := by decide +kernel
theorem sbd11_2_2 : ∀ q ∈ blkd11_2_2, subd11_2 q = true := by
  unfold blkd11_2_2
  exact List.forall_mem_cons.2 ⟨subd11_2_64, List.forall_mem_cons.2 ⟨subd11_2_65, List.forall_mem_cons.2 ⟨subd11_2_66, List.forall_mem_cons.2 ⟨subd11_2_67, List.forall_mem_cons.2 ⟨subd11_2_68, List.forall_mem_cons.2 ⟨subd11_2_69, List.forall_mem_cons.2 ⟨subd11_2_70, List.forall_mem_cons.2 ⟨subd11_2_71, List.forall_mem_cons.2 ⟨subd11_2_72, List.forall_mem_cons.2 ⟨subd11_2_73, List.forall_mem_cons.2 ⟨subd11_2_74, List.forall_mem_cons.2 ⟨subd11_2_75, List.forall_mem_cons.2 ⟨subd11_2_76, List.forall_mem_cons.2 ⟨subd11_2_77, List.forall_mem_cons.2 ⟨subd11_2_78, List.forall_mem_cons.2 ⟨subd11_2_79, List.forall_mem_cons.2 ⟨subd11_2_80, List.forall_mem_cons.2 ⟨subd11_2_81, List.forall_mem_cons.2 ⟨subd11_2_82, List.forall_mem_cons.2 ⟨subd11_2_83, List.forall_mem_cons.2 ⟨subd11_2_84, List.forall_mem_cons.2 ⟨subd11_2_85, List.forall_mem_cons.2 ⟨subd11_2_86, List.forall_mem_cons.2 ⟨subd11_2_87, List.forall_mem_cons.2 ⟨subd11_2_88, List.forall_mem_cons.2 ⟨subd11_2_89, List.forall_mem_cons.2 ⟨subd11_2_90, List.forall_mem_cons.2 ⟨subd11_2_91, List.forall_mem_cons.2 ⟨subd11_2_92, List.forall_mem_cons.2 ⟨subd11_2_93, List.forall_mem_cons.2 ⟨subd11_2_94, List.forall_mem_cons.2 ⟨subd11_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_96 : subd11_2 [0, -1, 1] = true := by decide +kernel
theorem subd11_2_97 : subd11_2 [0, -1, 2] = true := by decide +kernel
theorem subd11_2_98 : subd11_2 [0, -1, 3] = true := by decide +kernel
theorem subd11_2_99 : subd11_2 [0, -1, 4] = true := by decide +kernel
theorem subd11_2_100 : subd11_2 [0, -1, 5] = true := by decide +kernel
theorem subd11_2_101 : subd11_2 [0, -1, 6] = true := by decide +kernel
theorem subd11_2_102 : subd11_2 [0, -1, 7] = true := by decide +kernel
theorem subd11_2_103 : subd11_2 [0, -1, 8] = true := by decide +kernel
theorem subd11_2_104 : subd11_2 [0, 0, -10] = true := by decide +kernel
theorem subd11_2_105 : subd11_2 [0, 0, -9] = true := by decide +kernel
theorem subd11_2_106 : subd11_2 [0, 0, -8] = true := by decide +kernel
theorem subd11_2_107 : subd11_2 [0, 0, -7] = true := by decide +kernel
theorem subd11_2_108 : subd11_2 [0, 0, -6] = true := by decide +kernel
theorem subd11_2_109 : subd11_2 [0, 0, -5] = true := by decide +kernel
theorem subd11_2_110 : subd11_2 [0, 0, -4] = true := by decide +kernel
theorem subd11_2_111 : subd11_2 [0, 0, -3] = true := by decide +kernel
theorem subd11_2_112 : subd11_2 [0, 0, -2] = true := by decide +kernel
theorem subd11_2_113 : subd11_2 [0, 0, -1] = true := by decide +kernel
theorem subd11_2_114 : subd11_2 [0, 0, 0] = true := by decide +kernel
theorem subd11_2_115 : subd11_2 [0, 0, 1] = true := by decide +kernel
theorem subd11_2_116 : subd11_2 [0, 0, 2] = true := by decide +kernel
theorem subd11_2_117 : subd11_2 [0, 0, 3] = true := by decide +kernel
theorem subd11_2_118 : subd11_2 [0, 0, 4] = true := by decide +kernel
theorem subd11_2_119 : subd11_2 [0, 0, 5] = true := by decide +kernel
theorem subd11_2_120 : subd11_2 [0, 0, 6] = true := by decide +kernel
theorem subd11_2_121 : subd11_2 [0, 0, 7] = true := by decide +kernel
theorem subd11_2_122 : subd11_2 [0, 0, 8] = true := by decide +kernel
theorem subd11_2_123 : subd11_2 [0, 0, 9] = true := by decide +kernel
theorem subd11_2_124 : subd11_2 [0, 1, -9] = true := by decide +kernel
theorem subd11_2_125 : subd11_2 [0, 1, -8] = true := by decide +kernel
theorem subd11_2_126 : subd11_2 [0, 1, -7] = true := by decide +kernel
theorem subd11_2_127 : subd11_2 [0, 1, -6] = true := by decide +kernel
theorem sbd11_2_3 : ∀ q ∈ blkd11_2_3, subd11_2 q = true := by
  unfold blkd11_2_3
  exact List.forall_mem_cons.2 ⟨subd11_2_96, List.forall_mem_cons.2 ⟨subd11_2_97, List.forall_mem_cons.2 ⟨subd11_2_98, List.forall_mem_cons.2 ⟨subd11_2_99, List.forall_mem_cons.2 ⟨subd11_2_100, List.forall_mem_cons.2 ⟨subd11_2_101, List.forall_mem_cons.2 ⟨subd11_2_102, List.forall_mem_cons.2 ⟨subd11_2_103, List.forall_mem_cons.2 ⟨subd11_2_104, List.forall_mem_cons.2 ⟨subd11_2_105, List.forall_mem_cons.2 ⟨subd11_2_106, List.forall_mem_cons.2 ⟨subd11_2_107, List.forall_mem_cons.2 ⟨subd11_2_108, List.forall_mem_cons.2 ⟨subd11_2_109, List.forall_mem_cons.2 ⟨subd11_2_110, List.forall_mem_cons.2 ⟨subd11_2_111, List.forall_mem_cons.2 ⟨subd11_2_112, List.forall_mem_cons.2 ⟨subd11_2_113, List.forall_mem_cons.2 ⟨subd11_2_114, List.forall_mem_cons.2 ⟨subd11_2_115, List.forall_mem_cons.2 ⟨subd11_2_116, List.forall_mem_cons.2 ⟨subd11_2_117, List.forall_mem_cons.2 ⟨subd11_2_118, List.forall_mem_cons.2 ⟨subd11_2_119, List.forall_mem_cons.2 ⟨subd11_2_120, List.forall_mem_cons.2 ⟨subd11_2_121, List.forall_mem_cons.2 ⟨subd11_2_122, List.forall_mem_cons.2 ⟨subd11_2_123, List.forall_mem_cons.2 ⟨subd11_2_124, List.forall_mem_cons.2 ⟨subd11_2_125, List.forall_mem_cons.2 ⟨subd11_2_126, List.forall_mem_cons.2 ⟨subd11_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
