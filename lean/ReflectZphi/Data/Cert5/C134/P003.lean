import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_0_0 : subd1_0 [-3, -3] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [-3, -2] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [-3, -1] = true := by decide +kernel
theorem subd1_0_3 : subd1_0 [-3, 0] = true := by decide +kernel
theorem subd1_0_4 : subd1_0 [-3, 1] = true := by decide +kernel
theorem subd1_0_5 : subd1_0 [-3, 2] = true := by decide +kernel
theorem subd1_0_6 : subd1_0 [-3, 3] = true := by decide +kernel
theorem subd1_0_7 : subd1_0 [-2, -4] = true := by decide +kernel
theorem subd1_0_8 : subd1_0 [-2, -3] = true := by decide +kernel
theorem subd1_0_9 : subd1_0 [-2, -2] = true := by decide +kernel
theorem subd1_0_10 : subd1_0 [-2, -1] = true := by decide +kernel
theorem subd1_0_11 : subd1_0 [-2, 0] = true := by decide +kernel
theorem subd1_0_12 : subd1_0 [-2, 1] = true := by decide +kernel
theorem subd1_0_13 : subd1_0 [-2, 2] = true := by decide +kernel
theorem subd1_0_14 : subd1_0 [-2, 3] = true := by decide +kernel
theorem subd1_0_15 : subd1_0 [-1, -4] = true := by decide +kernel
theorem subd1_0_16 : subd1_0 [-1, -3] = true := by decide +kernel
theorem subd1_0_17 : subd1_0 [-1, -2] = true := by decide +kernel
theorem subd1_0_18 : subd1_0 [-1, -1] = true := by decide +kernel
theorem subd1_0_19 : subd1_0 [-1, 0] = true := by decide +kernel
theorem subd1_0_20 : subd1_0 [-1, 1] = true := by decide +kernel
theorem subd1_0_21 : subd1_0 [-1, 2] = true := by decide +kernel
theorem subd1_0_22 : subd1_0 [-1, 3] = true := by decide +kernel
theorem subd1_0_23 : subd1_0 [-1, 4] = true := by decide +kernel
theorem subd1_0_24 : subd1_0 [0, -5] = true := by decide +kernel
theorem subd1_0_25 : subd1_0 [0, -4] = true := by decide +kernel
theorem subd1_0_26 : subd1_0 [0, -3] = true := by decide +kernel
theorem subd1_0_27 : subd1_0 [0, -2] = true := by decide +kernel
theorem subd1_0_28 : subd1_0 [0, -1] = true := by decide +kernel
theorem subd1_0_29 : subd1_0 [0, 0] = true := by decide +kernel
theorem subd1_0_30 : subd1_0 [0, 1] = true := by decide +kernel
theorem subd1_0_31 : subd1_0 [0, 2] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_cons.2 ⟨subd1_0_3, List.forall_mem_cons.2 ⟨subd1_0_4, List.forall_mem_cons.2 ⟨subd1_0_5, List.forall_mem_cons.2 ⟨subd1_0_6, List.forall_mem_cons.2 ⟨subd1_0_7, List.forall_mem_cons.2 ⟨subd1_0_8, List.forall_mem_cons.2 ⟨subd1_0_9, List.forall_mem_cons.2 ⟨subd1_0_10, List.forall_mem_cons.2 ⟨subd1_0_11, List.forall_mem_cons.2 ⟨subd1_0_12, List.forall_mem_cons.2 ⟨subd1_0_13, List.forall_mem_cons.2 ⟨subd1_0_14, List.forall_mem_cons.2 ⟨subd1_0_15, List.forall_mem_cons.2 ⟨subd1_0_16, List.forall_mem_cons.2 ⟨subd1_0_17, List.forall_mem_cons.2 ⟨subd1_0_18, List.forall_mem_cons.2 ⟨subd1_0_19, List.forall_mem_cons.2 ⟨subd1_0_20, List.forall_mem_cons.2 ⟨subd1_0_21, List.forall_mem_cons.2 ⟨subd1_0_22, List.forall_mem_cons.2 ⟨subd1_0_23, List.forall_mem_cons.2 ⟨subd1_0_24, List.forall_mem_cons.2 ⟨subd1_0_25, List.forall_mem_cons.2 ⟨subd1_0_26, List.forall_mem_cons.2 ⟨subd1_0_27, List.forall_mem_cons.2 ⟨subd1_0_28, List.forall_mem_cons.2 ⟨subd1_0_29, List.forall_mem_cons.2 ⟨subd1_0_30, List.forall_mem_cons.2 ⟨subd1_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_0_32 : subd1_0 [0, 3] = true := by decide +kernel
theorem subd1_0_33 : subd1_0 [0, 4] = true := by decide +kernel
theorem subd1_0_34 : subd1_0 [1, -5] = true := by decide +kernel
theorem subd1_0_35 : subd1_0 [1, -4] = true := by decide +kernel
theorem subd1_0_36 : subd1_0 [1, -3] = true := by decide +kernel
theorem subd1_0_37 : subd1_0 [1, -2] = true := by decide +kernel
theorem subd1_0_38 : subd1_0 [1, -1] = true := by decide +kernel
theorem subd1_0_39 : subd1_0 [1, 0] = true := by decide +kernel
theorem subd1_0_40 : subd1_0 [1, 1] = true := by decide +kernel
theorem subd1_0_41 : subd1_0 [1, 2] = true := by decide +kernel
theorem subd1_0_42 : subd1_0 [1, 3] = true := by decide +kernel
theorem subd1_0_43 : subd1_0 [2, -4] = true := by decide +kernel
theorem subd1_0_44 : subd1_0 [2, -3] = true := by decide +kernel
theorem subd1_0_45 : subd1_0 [2, -2] = true := by decide +kernel
theorem subd1_0_46 : subd1_0 [2, -1] = true := by decide +kernel
theorem subd1_0_47 : subd1_0 [2, 0] = true := by decide +kernel
theorem subd1_0_48 : subd1_0 [2, 1] = true := by decide +kernel
theorem subd1_0_49 : subd1_0 [2, 2] = true := by decide +kernel
theorem subd1_0_50 : subd1_0 [2, 3] = true := by decide +kernel
theorem subd1_0_51 : subd1_0 [3, -4] = true := by decide +kernel
theorem subd1_0_52 : subd1_0 [3, -3] = true := by decide +kernel
theorem subd1_0_53 : subd1_0 [3, -2] = true := by decide +kernel
theorem subd1_0_54 : subd1_0 [3, -1] = true := by decide +kernel
theorem subd1_0_55 : subd1_0 [3, 0] = true := by decide +kernel
theorem subd1_0_56 : subd1_0 [3, 1] = true := by decide +kernel
theorem subd1_0_57 : subd1_0 [3, 2] = true := by decide +kernel
theorem sbd1_0_1 : ∀ q ∈ blkd1_0_1, subd1_0 q = true := by
  unfold blkd1_0_1
  exact List.forall_mem_cons.2 ⟨subd1_0_32, List.forall_mem_cons.2 ⟨subd1_0_33, List.forall_mem_cons.2 ⟨subd1_0_34, List.forall_mem_cons.2 ⟨subd1_0_35, List.forall_mem_cons.2 ⟨subd1_0_36, List.forall_mem_cons.2 ⟨subd1_0_37, List.forall_mem_cons.2 ⟨subd1_0_38, List.forall_mem_cons.2 ⟨subd1_0_39, List.forall_mem_cons.2 ⟨subd1_0_40, List.forall_mem_cons.2 ⟨subd1_0_41, List.forall_mem_cons.2 ⟨subd1_0_42, List.forall_mem_cons.2 ⟨subd1_0_43, List.forall_mem_cons.2 ⟨subd1_0_44, List.forall_mem_cons.2 ⟨subd1_0_45, List.forall_mem_cons.2 ⟨subd1_0_46, List.forall_mem_cons.2 ⟨subd1_0_47, List.forall_mem_cons.2 ⟨subd1_0_48, List.forall_mem_cons.2 ⟨subd1_0_49, List.forall_mem_cons.2 ⟨subd1_0_50, List.forall_mem_cons.2 ⟨subd1_0_51, List.forall_mem_cons.2 ⟨subd1_0_52, List.forall_mem_cons.2 ⟨subd1_0_53, List.forall_mem_cons.2 ⟨subd1_0_54, List.forall_mem_cons.2 ⟨subd1_0_55, List.forall_mem_cons.2 ⟨subd1_0_56, List.forall_mem_cons.2 ⟨subd1_0_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [-4] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [-3, -3] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [-3, -2] = true := by decide +kernel
theorem subd1_1_3 : subd1_1 [-3, -1] = true := by decide +kernel
theorem subd1_1_4 : subd1_1 [-3, 0] = true := by decide +kernel
theorem subd1_1_5 : subd1_1 [-3, 1] = true := by decide +kernel
theorem subd1_1_6 : subd1_1 [-3, 2] = true := by decide +kernel
theorem subd1_1_7 : subd1_1 [-3, 3] = true := by decide +kernel
theorem subd1_1_8 : subd1_1 [-3, 4] = true := by decide +kernel
theorem subd1_1_9 : subd1_1 [-2, -4] = true := by decide +kernel
theorem subd1_1_10 : subd1_1 [-2, -3] = true := by decide +kernel
theorem subd1_1_11 : subd1_1 [-2, -2] = true := by decide +kernel
theorem subd1_1_12 : subd1_1 [-2, -1] = true := by decide +kernel
theorem subd1_1_13 : subd1_1 [-2, 0] = true := by decide +kernel
theorem subd1_1_14 : subd1_1 [-2, 1] = true := by decide +kernel
theorem subd1_1_15 : subd1_1 [-2, 2] = true := by decide +kernel
theorem subd1_1_16 : subd1_1 [-2, 3] = true := by decide +kernel
theorem subd1_1_17 : subd1_1 [-2, 4] = true := by decide +kernel
theorem subd1_1_18 : subd1_1 [-2, 5] = true := by decide +kernel
theorem subd1_1_19 : subd1_1 [-1, -5] = true := by decide +kernel
theorem subd1_1_20 : subd1_1 [-1, -4] = true := by decide +kernel
theorem subd1_1_21 : subd1_1 [-1, -3] = true := by decide +kernel
theorem subd1_1_22 : subd1_1 [-1, -2] = true := by decide +kernel
theorem subd1_1_23 : subd1_1 [-1, -1] = true := by decide +kernel
theorem subd1_1_24 : subd1_1 [-1, 0] = true := by decide +kernel
theorem subd1_1_25 : subd1_1 [-1, 1] = true := by decide +kernel
theorem subd1_1_26 : subd1_1 [-1, 2] = true := by decide +kernel
theorem subd1_1_27 : subd1_1 [-1, 3] = true := by decide +kernel
theorem subd1_1_28 : subd1_1 [-1, 4] = true := by decide +kernel
theorem subd1_1_29 : subd1_1 [-1, 5] = true := by decide +kernel
theorem subd1_1_30 : subd1_1 [0, -5] = true := by decide +kernel
theorem subd1_1_31 : subd1_1 [0, -4] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_cons.2 ⟨subd1_1_3, List.forall_mem_cons.2 ⟨subd1_1_4, List.forall_mem_cons.2 ⟨subd1_1_5, List.forall_mem_cons.2 ⟨subd1_1_6, List.forall_mem_cons.2 ⟨subd1_1_7, List.forall_mem_cons.2 ⟨subd1_1_8, List.forall_mem_cons.2 ⟨subd1_1_9, List.forall_mem_cons.2 ⟨subd1_1_10, List.forall_mem_cons.2 ⟨subd1_1_11, List.forall_mem_cons.2 ⟨subd1_1_12, List.forall_mem_cons.2 ⟨subd1_1_13, List.forall_mem_cons.2 ⟨subd1_1_14, List.forall_mem_cons.2 ⟨subd1_1_15, List.forall_mem_cons.2 ⟨subd1_1_16, List.forall_mem_cons.2 ⟨subd1_1_17, List.forall_mem_cons.2 ⟨subd1_1_18, List.forall_mem_cons.2 ⟨subd1_1_19, List.forall_mem_cons.2 ⟨subd1_1_20, List.forall_mem_cons.2 ⟨subd1_1_21, List.forall_mem_cons.2 ⟨subd1_1_22, List.forall_mem_cons.2 ⟨subd1_1_23, List.forall_mem_cons.2 ⟨subd1_1_24, List.forall_mem_cons.2 ⟨subd1_1_25, List.forall_mem_cons.2 ⟨subd1_1_26, List.forall_mem_cons.2 ⟨subd1_1_27, List.forall_mem_cons.2 ⟨subd1_1_28, List.forall_mem_cons.2 ⟨subd1_1_29, List.forall_mem_cons.2 ⟨subd1_1_30, List.forall_mem_cons.2 ⟨subd1_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_1_32 : subd1_1 [0, -3] = true := by decide +kernel
theorem subd1_1_33 : subd1_1 [0, -2] = true := by decide +kernel
theorem subd1_1_34 : subd1_1 [0, -1] = true := by decide +kernel
theorem subd1_1_35 : subd1_1 [0, 0] = true := by decide +kernel
theorem subd1_1_36 : subd1_1 [0, 1] = true := by decide +kernel
theorem subd1_1_37 : subd1_1 [0, 2] = true := by decide +kernel
theorem subd1_1_38 : subd1_1 [0, 3] = true := by decide +kernel
theorem subd1_1_39 : subd1_1 [0, 4] = true := by decide +kernel
theorem subd1_1_40 : subd1_1 [1, -6] = true := by decide +kernel
theorem subd1_1_41 : subd1_1 [1, -5] = true := by decide +kernel
theorem subd1_1_42 : subd1_1 [1, -4] = true := by decide +kernel
theorem subd1_1_43 : subd1_1 [1, -3] = true := by decide +kernel
theorem subd1_1_44 : subd1_1 [1, -2] = true := by decide +kernel
theorem subd1_1_45 : subd1_1 [1, -1] = true := by decide +kernel
theorem subd1_1_46 : subd1_1 [1, 0] = true := by decide +kernel
theorem subd1_1_47 : subd1_1 [1, 1] = true := by decide +kernel
theorem subd1_1_48 : subd1_1 [1, 2] = true := by decide +kernel
theorem subd1_1_49 : subd1_1 [1, 3] = true := by decide +kernel
theorem subd1_1_50 : subd1_1 [1, 4] = true := by decide +kernel
theorem subd1_1_51 : subd1_1 [2, -6] = true := by decide +kernel
theorem subd1_1_52 : subd1_1 [2, -5] = true := by decide +kernel
theorem subd1_1_53 : subd1_1 [2, -4] = true := by decide +kernel
theorem subd1_1_54 : subd1_1 [2, -3] = true := by decide +kernel
theorem subd1_1_55 : subd1_1 [2, -2] = true := by decide +kernel
theorem subd1_1_56 : subd1_1 [2, -1] = true := by decide +kernel
theorem subd1_1_57 : subd1_1 [2, 0] = true := by decide +kernel
theorem subd1_1_58 : subd1_1 [2, 1] = true := by decide +kernel
theorem subd1_1_59 : subd1_1 [2, 2] = true := by decide +kernel
theorem subd1_1_60 : subd1_1 [2, 3] = true := by decide +kernel
theorem subd1_1_61 : subd1_1 [3, -5] = true := by decide +kernel
theorem subd1_1_62 : subd1_1 [3, -4] = true := by decide +kernel
theorem subd1_1_63 : subd1_1 [3, -3] = true := by decide +kernel
theorem sbd1_1_1 : ∀ q ∈ blkd1_1_1, subd1_1 q = true := by
  unfold blkd1_1_1
  exact List.forall_mem_cons.2 ⟨subd1_1_32, List.forall_mem_cons.2 ⟨subd1_1_33, List.forall_mem_cons.2 ⟨subd1_1_34, List.forall_mem_cons.2 ⟨subd1_1_35, List.forall_mem_cons.2 ⟨subd1_1_36, List.forall_mem_cons.2 ⟨subd1_1_37, List.forall_mem_cons.2 ⟨subd1_1_38, List.forall_mem_cons.2 ⟨subd1_1_39, List.forall_mem_cons.2 ⟨subd1_1_40, List.forall_mem_cons.2 ⟨subd1_1_41, List.forall_mem_cons.2 ⟨subd1_1_42, List.forall_mem_cons.2 ⟨subd1_1_43, List.forall_mem_cons.2 ⟨subd1_1_44, List.forall_mem_cons.2 ⟨subd1_1_45, List.forall_mem_cons.2 ⟨subd1_1_46, List.forall_mem_cons.2 ⟨subd1_1_47, List.forall_mem_cons.2 ⟨subd1_1_48, List.forall_mem_cons.2 ⟨subd1_1_49, List.forall_mem_cons.2 ⟨subd1_1_50, List.forall_mem_cons.2 ⟨subd1_1_51, List.forall_mem_cons.2 ⟨subd1_1_52, List.forall_mem_cons.2 ⟨subd1_1_53, List.forall_mem_cons.2 ⟨subd1_1_54, List.forall_mem_cons.2 ⟨subd1_1_55, List.forall_mem_cons.2 ⟨subd1_1_56, List.forall_mem_cons.2 ⟨subd1_1_57, List.forall_mem_cons.2 ⟨subd1_1_58, List.forall_mem_cons.2 ⟨subd1_1_59, List.forall_mem_cons.2 ⟨subd1_1_60, List.forall_mem_cons.2 ⟨subd1_1_61, List.forall_mem_cons.2 ⟨subd1_1_62, List.forall_mem_cons.2 ⟨subd1_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_1_64 : subd1_1 [3, -2] = true := by decide +kernel
theorem subd1_1_65 : subd1_1 [3, -1] = true := by decide +kernel
theorem subd1_1_66 : subd1_1 [3, 0] = true := by decide +kernel
theorem subd1_1_67 : subd1_1 [3, 1] = true := by decide +kernel
theorem subd1_1_68 : subd1_1 [3, 2] = true := by decide +kernel
theorem subd1_1_69 : subd1_1 [4] = true := by decide +kernel
theorem sbd1_1_2 : ∀ q ∈ blkd1_1_2, subd1_1 q = true := by
  unfold blkd1_1_2
  exact List.forall_mem_cons.2 ⟨subd1_1_64, List.forall_mem_cons.2 ⟨subd1_1_65, List.forall_mem_cons.2 ⟨subd1_1_66, List.forall_mem_cons.2 ⟨subd1_1_67, List.forall_mem_cons.2 ⟨subd1_1_68, List.forall_mem_cons.2 ⟨subd1_1_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
