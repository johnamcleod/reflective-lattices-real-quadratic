import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_2_0 : subd1_2 [-4] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-3, -4] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [-3, -3] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [-3, -2] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [-3, -1] = true := by decide +kernel
theorem subd1_2_5 : subd1_2 [-3, 0] = true := by decide +kernel
theorem subd1_2_6 : subd1_2 [-3, 1] = true := by decide +kernel
theorem subd1_2_7 : subd1_2 [-3, 2] = true := by decide +kernel
theorem subd1_2_8 : subd1_2 [-2, -5] = true := by decide +kernel
theorem subd1_2_9 : subd1_2 [-2, -4] = true := by decide +kernel
theorem subd1_2_10 : subd1_2 [-2, -3] = true := by decide +kernel
theorem subd1_2_11 : subd1_2 [-2, -2] = true := by decide +kernel
theorem subd1_2_12 : subd1_2 [-2, -1] = true := by decide +kernel
theorem subd1_2_13 : subd1_2 [-2, 0] = true := by decide +kernel
theorem subd1_2_14 : subd1_2 [-2, 1] = true := by decide +kernel
theorem subd1_2_15 : subd1_2 [-2, 2] = true := by decide +kernel
theorem subd1_2_16 : subd1_2 [-2, 3] = true := by decide +kernel
theorem subd1_2_17 : subd1_2 [-1, -5] = true := by decide +kernel
theorem subd1_2_18 : subd1_2 [-1, -4] = true := by decide +kernel
theorem subd1_2_19 : subd1_2 [-1, -3] = true := by decide +kernel
theorem subd1_2_20 : subd1_2 [-1, -2] = true := by decide +kernel
theorem subd1_2_21 : subd1_2 [-1, -1] = true := by decide +kernel
theorem subd1_2_22 : subd1_2 [-1, 0] = true := by decide +kernel
theorem subd1_2_23 : subd1_2 [-1, 1] = true := by decide +kernel
theorem subd1_2_24 : subd1_2 [-1, 2] = true := by decide +kernel
theorem subd1_2_25 : subd1_2 [-1, 3] = true := by decide +kernel
theorem subd1_2_26 : subd1_2 [0, -5] = true := by decide +kernel
theorem subd1_2_27 : subd1_2 [0, -4] = true := by decide +kernel
theorem subd1_2_28 : subd1_2 [0, -3] = true := by decide +kernel
theorem subd1_2_29 : subd1_2 [0, -2] = true := by decide +kernel
theorem subd1_2_30 : subd1_2 [0, -1] = true := by decide +kernel
theorem subd1_2_31 : subd1_2 [0, 0] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_cons.2 ⟨subd1_2_5, List.forall_mem_cons.2 ⟨subd1_2_6, List.forall_mem_cons.2 ⟨subd1_2_7, List.forall_mem_cons.2 ⟨subd1_2_8, List.forall_mem_cons.2 ⟨subd1_2_9, List.forall_mem_cons.2 ⟨subd1_2_10, List.forall_mem_cons.2 ⟨subd1_2_11, List.forall_mem_cons.2 ⟨subd1_2_12, List.forall_mem_cons.2 ⟨subd1_2_13, List.forall_mem_cons.2 ⟨subd1_2_14, List.forall_mem_cons.2 ⟨subd1_2_15, List.forall_mem_cons.2 ⟨subd1_2_16, List.forall_mem_cons.2 ⟨subd1_2_17, List.forall_mem_cons.2 ⟨subd1_2_18, List.forall_mem_cons.2 ⟨subd1_2_19, List.forall_mem_cons.2 ⟨subd1_2_20, List.forall_mem_cons.2 ⟨subd1_2_21, List.forall_mem_cons.2 ⟨subd1_2_22, List.forall_mem_cons.2 ⟨subd1_2_23, List.forall_mem_cons.2 ⟨subd1_2_24, List.forall_mem_cons.2 ⟨subd1_2_25, List.forall_mem_cons.2 ⟨subd1_2_26, List.forall_mem_cons.2 ⟨subd1_2_27, List.forall_mem_cons.2 ⟨subd1_2_28, List.forall_mem_cons.2 ⟨subd1_2_29, List.forall_mem_cons.2 ⟨subd1_2_30, List.forall_mem_cons.2 ⟨subd1_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_2_32 : subd1_2 [0, 1] = true := by decide +kernel
theorem subd1_2_33 : subd1_2 [0, 2] = true := by decide +kernel
theorem subd1_2_34 : subd1_2 [0, 3] = true := by decide +kernel
theorem subd1_2_35 : subd1_2 [0, 4] = true := by decide +kernel
theorem subd1_2_36 : subd1_2 [1, -4] = true := by decide +kernel
theorem subd1_2_37 : subd1_2 [1, -3] = true := by decide +kernel
theorem subd1_2_38 : subd1_2 [1, -2] = true := by decide +kernel
theorem subd1_2_39 : subd1_2 [1, -1] = true := by decide +kernel
theorem subd1_2_40 : subd1_2 [1, 0] = true := by decide +kernel
theorem subd1_2_41 : subd1_2 [1, 1] = true := by decide +kernel
theorem subd1_2_42 : subd1_2 [1, 2] = true := by decide +kernel
theorem subd1_2_43 : subd1_2 [1, 3] = true := by decide +kernel
theorem subd1_2_44 : subd1_2 [1, 4] = true := by decide +kernel
theorem subd1_2_45 : subd1_2 [2, -4] = true := by decide +kernel
theorem subd1_2_46 : subd1_2 [2, -3] = true := by decide +kernel
theorem subd1_2_47 : subd1_2 [2, -2] = true := by decide +kernel
theorem subd1_2_48 : subd1_2 [2, -1] = true := by decide +kernel
theorem subd1_2_49 : subd1_2 [2, 0] = true := by decide +kernel
theorem subd1_2_50 : subd1_2 [2, 1] = true := by decide +kernel
theorem subd1_2_51 : subd1_2 [2, 2] = true := by decide +kernel
theorem subd1_2_52 : subd1_2 [2, 3] = true := by decide +kernel
theorem subd1_2_53 : subd1_2 [2, 4] = true := by decide +kernel
theorem subd1_2_54 : subd1_2 [3, -3] = true := by decide +kernel
theorem subd1_2_55 : subd1_2 [3, -2] = true := by decide +kernel
theorem subd1_2_56 : subd1_2 [3, -1] = true := by decide +kernel
theorem subd1_2_57 : subd1_2 [3, 0] = true := by decide +kernel
theorem subd1_2_58 : subd1_2 [3, 1] = true := by decide +kernel
theorem subd1_2_59 : subd1_2 [3, 2] = true := by decide +kernel
theorem subd1_2_60 : subd1_2 [3, 3] = true := by decide +kernel
theorem subd1_2_61 : subd1_2 [4] = true := by decide +kernel
theorem sbd1_2_1 : ∀ q ∈ blkd1_2_1, subd1_2 q = true := by
  unfold blkd1_2_1
  exact List.forall_mem_cons.2 ⟨subd1_2_32, List.forall_mem_cons.2 ⟨subd1_2_33, List.forall_mem_cons.2 ⟨subd1_2_34, List.forall_mem_cons.2 ⟨subd1_2_35, List.forall_mem_cons.2 ⟨subd1_2_36, List.forall_mem_cons.2 ⟨subd1_2_37, List.forall_mem_cons.2 ⟨subd1_2_38, List.forall_mem_cons.2 ⟨subd1_2_39, List.forall_mem_cons.2 ⟨subd1_2_40, List.forall_mem_cons.2 ⟨subd1_2_41, List.forall_mem_cons.2 ⟨subd1_2_42, List.forall_mem_cons.2 ⟨subd1_2_43, List.forall_mem_cons.2 ⟨subd1_2_44, List.forall_mem_cons.2 ⟨subd1_2_45, List.forall_mem_cons.2 ⟨subd1_2_46, List.forall_mem_cons.2 ⟨subd1_2_47, List.forall_mem_cons.2 ⟨subd1_2_48, List.forall_mem_cons.2 ⟨subd1_2_49, List.forall_mem_cons.2 ⟨subd1_2_50, List.forall_mem_cons.2 ⟨subd1_2_51, List.forall_mem_cons.2 ⟨subd1_2_52, List.forall_mem_cons.2 ⟨subd1_2_53, List.forall_mem_cons.2 ⟨subd1_2_54, List.forall_mem_cons.2 ⟨subd1_2_55, List.forall_mem_cons.2 ⟨subd1_2_56, List.forall_mem_cons.2 ⟨subd1_2_57, List.forall_mem_cons.2 ⟨subd1_2_58, List.forall_mem_cons.2 ⟨subd1_2_59, List.forall_mem_cons.2 ⟨subd1_2_60, List.forall_mem_cons.2 ⟨subd1_2_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-5] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-4] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [-3, -3] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [-3, -2] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [-3, -1] = true := by decide +kernel
theorem subd1_3_5 : subd1_3 [-3, 0] = true := by decide +kernel
theorem subd1_3_6 : subd1_3 [-3, 1] = true := by decide +kernel
theorem subd1_3_7 : subd1_3 [-3, 2] = true := by decide +kernel
theorem subd1_3_8 : subd1_3 [-3, 3] = true := by decide +kernel
theorem subd1_3_9 : subd1_3 [-3, 4] = true := by decide +kernel
theorem subd1_3_10 : subd1_3 [-2, -4] = true := by decide +kernel
theorem subd1_3_11 : subd1_3 [-2, -3] = true := by decide +kernel
theorem subd1_3_12 : subd1_3 [-2, -2] = true := by decide +kernel
theorem subd1_3_13 : subd1_3 [-2, -1] = true := by decide +kernel
theorem subd1_3_14 : subd1_3 [-2, 0] = true := by decide +kernel
theorem subd1_3_15 : subd1_3 [-2, 1] = true := by decide +kernel
theorem subd1_3_16 : subd1_3 [-2, 2] = true := by decide +kernel
theorem subd1_3_17 : subd1_3 [-2, 3] = true := by decide +kernel
theorem subd1_3_18 : subd1_3 [-2, 4] = true := by decide +kernel
theorem subd1_3_19 : subd1_3 [-1, -4] = true := by decide +kernel
theorem subd1_3_20 : subd1_3 [-1, -3] = true := by decide +kernel
theorem subd1_3_21 : subd1_3 [-1, -2] = true := by decide +kernel
theorem subd1_3_22 : subd1_3 [-1, -1] = true := by decide +kernel
theorem subd1_3_23 : subd1_3 [-1, 0] = true := by decide +kernel
theorem subd1_3_24 : subd1_3 [-1, 1] = true := by decide +kernel
theorem subd1_3_25 : subd1_3 [-1, 2] = true := by decide +kernel
theorem subd1_3_26 : subd1_3 [-1, 3] = true := by decide +kernel
theorem subd1_3_27 : subd1_3 [-1, 4] = true := by decide +kernel
theorem subd1_3_28 : subd1_3 [0, -5] = true := by decide +kernel
theorem subd1_3_29 : subd1_3 [0, -4] = true := by decide +kernel
theorem subd1_3_30 : subd1_3 [0, -3] = true := by decide +kernel
theorem subd1_3_31 : subd1_3 [0, -2] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_cons.2 ⟨subd1_3_5, List.forall_mem_cons.2 ⟨subd1_3_6, List.forall_mem_cons.2 ⟨subd1_3_7, List.forall_mem_cons.2 ⟨subd1_3_8, List.forall_mem_cons.2 ⟨subd1_3_9, List.forall_mem_cons.2 ⟨subd1_3_10, List.forall_mem_cons.2 ⟨subd1_3_11, List.forall_mem_cons.2 ⟨subd1_3_12, List.forall_mem_cons.2 ⟨subd1_3_13, List.forall_mem_cons.2 ⟨subd1_3_14, List.forall_mem_cons.2 ⟨subd1_3_15, List.forall_mem_cons.2 ⟨subd1_3_16, List.forall_mem_cons.2 ⟨subd1_3_17, List.forall_mem_cons.2 ⟨subd1_3_18, List.forall_mem_cons.2 ⟨subd1_3_19, List.forall_mem_cons.2 ⟨subd1_3_20, List.forall_mem_cons.2 ⟨subd1_3_21, List.forall_mem_cons.2 ⟨subd1_3_22, List.forall_mem_cons.2 ⟨subd1_3_23, List.forall_mem_cons.2 ⟨subd1_3_24, List.forall_mem_cons.2 ⟨subd1_3_25, List.forall_mem_cons.2 ⟨subd1_3_26, List.forall_mem_cons.2 ⟨subd1_3_27, List.forall_mem_cons.2 ⟨subd1_3_28, List.forall_mem_cons.2 ⟨subd1_3_29, List.forall_mem_cons.2 ⟨subd1_3_30, List.forall_mem_cons.2 ⟨subd1_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_3_32 : subd1_3 [0, -1] = true := by decide +kernel
theorem subd1_3_33 : subd1_3 [0, 0] = true := by decide +kernel
theorem subd1_3_34 : subd1_3 [0, 1] = true := by decide +kernel
theorem subd1_3_35 : subd1_3 [0, 2] = true := by decide +kernel
theorem subd1_3_36 : subd1_3 [0, 3] = true := by decide +kernel
theorem subd1_3_37 : subd1_3 [0, 4] = true := by decide +kernel
theorem subd1_3_38 : subd1_3 [1, -5] = true := by decide +kernel
theorem subd1_3_39 : subd1_3 [1, -4] = true := by decide +kernel
theorem subd1_3_40 : subd1_3 [1, -3] = true := by decide +kernel
theorem subd1_3_41 : subd1_3 [1, -2] = true := by decide +kernel
theorem subd1_3_42 : subd1_3 [1, -1] = true := by decide +kernel
theorem subd1_3_43 : subd1_3 [1, 0] = true := by decide +kernel
theorem subd1_3_44 : subd1_3 [1, 1] = true := by decide +kernel
theorem subd1_3_45 : subd1_3 [1, 2] = true := by decide +kernel
theorem subd1_3_46 : subd1_3 [1, 3] = true := by decide +kernel
theorem subd1_3_47 : subd1_3 [2, -5] = true := by decide +kernel
theorem subd1_3_48 : subd1_3 [2, -4] = true := by decide +kernel
theorem subd1_3_49 : subd1_3 [2, -3] = true := by decide +kernel
theorem subd1_3_50 : subd1_3 [2, -2] = true := by decide +kernel
theorem subd1_3_51 : subd1_3 [2, -1] = true := by decide +kernel
theorem subd1_3_52 : subd1_3 [2, 0] = true := by decide +kernel
theorem subd1_3_53 : subd1_3 [2, 1] = true := by decide +kernel
theorem subd1_3_54 : subd1_3 [2, 2] = true := by decide +kernel
theorem subd1_3_55 : subd1_3 [2, 3] = true := by decide +kernel
theorem subd1_3_56 : subd1_3 [3, -5] = true := by decide +kernel
theorem subd1_3_57 : subd1_3 [3, -4] = true := by decide +kernel
theorem subd1_3_58 : subd1_3 [3, -3] = true := by decide +kernel
theorem subd1_3_59 : subd1_3 [3, -2] = true := by decide +kernel
theorem subd1_3_60 : subd1_3 [3, -1] = true := by decide +kernel
theorem subd1_3_61 : subd1_3 [3, 0] = true := by decide +kernel
theorem subd1_3_62 : subd1_3 [3, 1] = true := by decide +kernel
theorem subd1_3_63 : subd1_3 [3, 2] = true := by decide +kernel
theorem sbd1_3_1 : ∀ q ∈ blkd1_3_1, subd1_3 q = true := by
  unfold blkd1_3_1
  exact List.forall_mem_cons.2 ⟨subd1_3_32, List.forall_mem_cons.2 ⟨subd1_3_33, List.forall_mem_cons.2 ⟨subd1_3_34, List.forall_mem_cons.2 ⟨subd1_3_35, List.forall_mem_cons.2 ⟨subd1_3_36, List.forall_mem_cons.2 ⟨subd1_3_37, List.forall_mem_cons.2 ⟨subd1_3_38, List.forall_mem_cons.2 ⟨subd1_3_39, List.forall_mem_cons.2 ⟨subd1_3_40, List.forall_mem_cons.2 ⟨subd1_3_41, List.forall_mem_cons.2 ⟨subd1_3_42, List.forall_mem_cons.2 ⟨subd1_3_43, List.forall_mem_cons.2 ⟨subd1_3_44, List.forall_mem_cons.2 ⟨subd1_3_45, List.forall_mem_cons.2 ⟨subd1_3_46, List.forall_mem_cons.2 ⟨subd1_3_47, List.forall_mem_cons.2 ⟨subd1_3_48, List.forall_mem_cons.2 ⟨subd1_3_49, List.forall_mem_cons.2 ⟨subd1_3_50, List.forall_mem_cons.2 ⟨subd1_3_51, List.forall_mem_cons.2 ⟨subd1_3_52, List.forall_mem_cons.2 ⟨subd1_3_53, List.forall_mem_cons.2 ⟨subd1_3_54, List.forall_mem_cons.2 ⟨subd1_3_55, List.forall_mem_cons.2 ⟨subd1_3_56, List.forall_mem_cons.2 ⟨subd1_3_57, List.forall_mem_cons.2 ⟨subd1_3_58, List.forall_mem_cons.2 ⟨subd1_3_59, List.forall_mem_cons.2 ⟨subd1_3_60, List.forall_mem_cons.2 ⟨subd1_3_61, List.forall_mem_cons.2 ⟨subd1_3_62, List.forall_mem_cons.2 ⟨subd1_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_3_64 : subd1_3 [4] = true := by decide +kernel
theorem subd1_3_65 : subd1_3 [5] = true := by decide +kernel
theorem sbd1_3_2 : ∀ q ∈ blkd1_3_2, subd1_3 q = true := by
  unfold blkd1_3_2
  exact List.forall_mem_cons.2 ⟨subd1_3_64, List.forall_mem_cons.2 ⟨subd1_3_65, List.forall_mem_nil _⟩⟩
theorem ld_okd1_4 : ldCheck G d1_4.U d1_4.ms ldd1_4 = true := by decide +kernel
theorem pre_okd1_4 : subPre G cell1 d1_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
