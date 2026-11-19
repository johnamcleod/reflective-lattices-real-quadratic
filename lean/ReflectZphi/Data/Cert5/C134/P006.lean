import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_6_0 : subd1_6 [-4] = true := by decide +kernel
theorem subd1_6_1 : subd1_6 [-3, -5] = true := by decide +kernel
theorem subd1_6_2 : subd1_6 [-3, -4] = true := by decide +kernel
theorem subd1_6_3 : subd1_6 [-3, -3] = true := by decide +kernel
theorem subd1_6_4 : subd1_6 [-3, -2] = true := by decide +kernel
theorem subd1_6_5 : subd1_6 [-3, -1] = true := by decide +kernel
theorem subd1_6_6 : subd1_6 [-3, 0] = true := by decide +kernel
theorem subd1_6_7 : subd1_6 [-3, 1] = true := by decide +kernel
theorem subd1_6_8 : subd1_6 [-3, 2] = true := by decide +kernel
theorem subd1_6_9 : subd1_6 [-2, -5] = true := by decide +kernel
theorem subd1_6_10 : subd1_6 [-2, -4] = true := by decide +kernel
theorem subd1_6_11 : subd1_6 [-2, -3] = true := by decide +kernel
theorem subd1_6_12 : subd1_6 [-2, -2] = true := by decide +kernel
theorem subd1_6_13 : subd1_6 [-2, -1] = true := by decide +kernel
theorem subd1_6_14 : subd1_6 [-2, 0] = true := by decide +kernel
theorem subd1_6_15 : subd1_6 [-2, 1] = true := by decide +kernel
theorem subd1_6_16 : subd1_6 [-2, 2] = true := by decide +kernel
theorem subd1_6_17 : subd1_6 [-2, 3] = true := by decide +kernel
theorem subd1_6_18 : subd1_6 [-1, -5] = true := by decide +kernel
theorem subd1_6_19 : subd1_6 [-1, -4] = true := by decide +kernel
theorem subd1_6_20 : subd1_6 [-1, -3] = true := by decide +kernel
theorem subd1_6_21 : subd1_6 [-1, -2] = true := by decide +kernel
theorem subd1_6_22 : subd1_6 [-1, -1] = true := by decide +kernel
theorem subd1_6_23 : subd1_6 [-1, 0] = true := by decide +kernel
theorem subd1_6_24 : subd1_6 [-1, 1] = true := by decide +kernel
theorem subd1_6_25 : subd1_6 [-1, 2] = true := by decide +kernel
theorem subd1_6_26 : subd1_6 [-1, 3] = true := by decide +kernel
theorem subd1_6_27 : subd1_6 [0, -5] = true := by decide +kernel
theorem subd1_6_28 : subd1_6 [0, -4] = true := by decide +kernel
theorem subd1_6_29 : subd1_6 [0, -3] = true := by decide +kernel
theorem subd1_6_30 : subd1_6 [0, -2] = true := by decide +kernel
theorem subd1_6_31 : subd1_6 [0, -1] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_cons.2 ⟨subd1_6_1, List.forall_mem_cons.2 ⟨subd1_6_2, List.forall_mem_cons.2 ⟨subd1_6_3, List.forall_mem_cons.2 ⟨subd1_6_4, List.forall_mem_cons.2 ⟨subd1_6_5, List.forall_mem_cons.2 ⟨subd1_6_6, List.forall_mem_cons.2 ⟨subd1_6_7, List.forall_mem_cons.2 ⟨subd1_6_8, List.forall_mem_cons.2 ⟨subd1_6_9, List.forall_mem_cons.2 ⟨subd1_6_10, List.forall_mem_cons.2 ⟨subd1_6_11, List.forall_mem_cons.2 ⟨subd1_6_12, List.forall_mem_cons.2 ⟨subd1_6_13, List.forall_mem_cons.2 ⟨subd1_6_14, List.forall_mem_cons.2 ⟨subd1_6_15, List.forall_mem_cons.2 ⟨subd1_6_16, List.forall_mem_cons.2 ⟨subd1_6_17, List.forall_mem_cons.2 ⟨subd1_6_18, List.forall_mem_cons.2 ⟨subd1_6_19, List.forall_mem_cons.2 ⟨subd1_6_20, List.forall_mem_cons.2 ⟨subd1_6_21, List.forall_mem_cons.2 ⟨subd1_6_22, List.forall_mem_cons.2 ⟨subd1_6_23, List.forall_mem_cons.2 ⟨subd1_6_24, List.forall_mem_cons.2 ⟨subd1_6_25, List.forall_mem_cons.2 ⟨subd1_6_26, List.forall_mem_cons.2 ⟨subd1_6_27, List.forall_mem_cons.2 ⟨subd1_6_28, List.forall_mem_cons.2 ⟨subd1_6_29, List.forall_mem_cons.2 ⟨subd1_6_30, List.forall_mem_cons.2 ⟨subd1_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_6_32 : subd1_6 [0, 0] = true := by decide +kernel
theorem subd1_6_33 : subd1_6 [0, 1] = true := by decide +kernel
theorem subd1_6_34 : subd1_6 [0, 2] = true := by decide +kernel
theorem subd1_6_35 : subd1_6 [0, 3] = true := by decide +kernel
theorem subd1_6_36 : subd1_6 [0, 4] = true := by decide +kernel
theorem subd1_6_37 : subd1_6 [1, -4] = true := by decide +kernel
theorem subd1_6_38 : subd1_6 [1, -3] = true := by decide +kernel
theorem subd1_6_39 : subd1_6 [1, -2] = true := by decide +kernel
theorem subd1_6_40 : subd1_6 [1, -1] = true := by decide +kernel
theorem subd1_6_41 : subd1_6 [1, 0] = true := by decide +kernel
theorem subd1_6_42 : subd1_6 [1, 1] = true := by decide +kernel
theorem subd1_6_43 : subd1_6 [1, 2] = true := by decide +kernel
theorem subd1_6_44 : subd1_6 [1, 3] = true := by decide +kernel
theorem subd1_6_45 : subd1_6 [1, 4] = true := by decide +kernel
theorem subd1_6_46 : subd1_6 [2, -4] = true := by decide +kernel
theorem subd1_6_47 : subd1_6 [2, -3] = true := by decide +kernel
theorem subd1_6_48 : subd1_6 [2, -2] = true := by decide +kernel
theorem subd1_6_49 : subd1_6 [2, -1] = true := by decide +kernel
theorem subd1_6_50 : subd1_6 [2, 0] = true := by decide +kernel
theorem subd1_6_51 : subd1_6 [2, 1] = true := by decide +kernel
theorem subd1_6_52 : subd1_6 [2, 2] = true := by decide +kernel
theorem subd1_6_53 : subd1_6 [2, 3] = true := by decide +kernel
theorem subd1_6_54 : subd1_6 [2, 4] = true := by decide +kernel
theorem subd1_6_55 : subd1_6 [3, -3] = true := by decide +kernel
theorem subd1_6_56 : subd1_6 [3, -2] = true := by decide +kernel
theorem subd1_6_57 : subd1_6 [3, -1] = true := by decide +kernel
theorem subd1_6_58 : subd1_6 [3, 0] = true := by decide +kernel
theorem subd1_6_59 : subd1_6 [3, 1] = true := by decide +kernel
theorem subd1_6_60 : subd1_6 [3, 2] = true := by decide +kernel
theorem subd1_6_61 : subd1_6 [3, 3] = true := by decide +kernel
theorem subd1_6_62 : subd1_6 [3, 4] = true := by decide +kernel
theorem subd1_6_63 : subd1_6 [4] = true := by decide +kernel
theorem sbd1_6_1 : ∀ q ∈ blkd1_6_1, subd1_6 q = true := by
  unfold blkd1_6_1
  exact List.forall_mem_cons.2 ⟨subd1_6_32, List.forall_mem_cons.2 ⟨subd1_6_33, List.forall_mem_cons.2 ⟨subd1_6_34, List.forall_mem_cons.2 ⟨subd1_6_35, List.forall_mem_cons.2 ⟨subd1_6_36, List.forall_mem_cons.2 ⟨subd1_6_37, List.forall_mem_cons.2 ⟨subd1_6_38, List.forall_mem_cons.2 ⟨subd1_6_39, List.forall_mem_cons.2 ⟨subd1_6_40, List.forall_mem_cons.2 ⟨subd1_6_41, List.forall_mem_cons.2 ⟨subd1_6_42, List.forall_mem_cons.2 ⟨subd1_6_43, List.forall_mem_cons.2 ⟨subd1_6_44, List.forall_mem_cons.2 ⟨subd1_6_45, List.forall_mem_cons.2 ⟨subd1_6_46, List.forall_mem_cons.2 ⟨subd1_6_47, List.forall_mem_cons.2 ⟨subd1_6_48, List.forall_mem_cons.2 ⟨subd1_6_49, List.forall_mem_cons.2 ⟨subd1_6_50, List.forall_mem_cons.2 ⟨subd1_6_51, List.forall_mem_cons.2 ⟨subd1_6_52, List.forall_mem_cons.2 ⟨subd1_6_53, List.forall_mem_cons.2 ⟨subd1_6_54, List.forall_mem_cons.2 ⟨subd1_6_55, List.forall_mem_cons.2 ⟨subd1_6_56, List.forall_mem_cons.2 ⟨subd1_6_57, List.forall_mem_cons.2 ⟨subd1_6_58, List.forall_mem_cons.2 ⟨subd1_6_59, List.forall_mem_cons.2 ⟨subd1_6_60, List.forall_mem_cons.2 ⟨subd1_6_61, List.forall_mem_cons.2 ⟨subd1_6_62, List.forall_mem_cons.2 ⟨subd1_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_7 : ldCheck G d1_7.U d1_7.ms ldd1_7 = true := by decide +kernel
theorem pre_okd1_7 : subPre G cell1 d1_7 = true := by decide +kernel
theorem subd1_7_0 : subd1_7 [-4] = true := by decide +kernel
theorem subd1_7_1 : subd1_7 [-3, -4] = true := by decide +kernel
theorem subd1_7_2 : subd1_7 [-3, -3] = true := by decide +kernel
theorem subd1_7_3 : subd1_7 [-3, -2] = true := by decide +kernel
theorem subd1_7_4 : subd1_7 [-3, -1] = true := by decide +kernel
theorem subd1_7_5 : subd1_7 [-3, 0] = true := by decide +kernel
theorem subd1_7_6 : subd1_7 [-3, 1] = true := by decide +kernel
theorem subd1_7_7 : subd1_7 [-3, 2] = true := by decide +kernel
theorem subd1_7_8 : subd1_7 [-3, 3] = true := by decide +kernel
theorem subd1_7_9 : subd1_7 [-2, -4] = true := by decide +kernel
theorem subd1_7_10 : subd1_7 [-2, -3] = true := by decide +kernel
theorem subd1_7_11 : subd1_7 [-2, -2] = true := by decide +kernel
theorem subd1_7_12 : subd1_7 [-2, -1] = true := by decide +kernel
theorem subd1_7_13 : subd1_7 [-2, 0] = true := by decide +kernel
theorem subd1_7_14 : subd1_7 [-2, 1] = true := by decide +kernel
theorem subd1_7_15 : subd1_7 [-2, 2] = true := by decide +kernel
theorem subd1_7_16 : subd1_7 [-2, 3] = true := by decide +kernel
theorem subd1_7_17 : subd1_7 [-1, -5] = true := by decide +kernel
theorem subd1_7_18 : subd1_7 [-1, -4] = true := by decide +kernel
theorem subd1_7_19 : subd1_7 [-1, -3] = true := by decide +kernel
theorem subd1_7_20 : subd1_7 [-1, -2] = true := by decide +kernel
theorem subd1_7_21 : subd1_7 [-1, -1] = true := by decide +kernel
theorem subd1_7_22 : subd1_7 [-1, 0] = true := by decide +kernel
theorem subd1_7_23 : subd1_7 [-1, 1] = true := by decide +kernel
theorem subd1_7_24 : subd1_7 [-1, 2] = true := by decide +kernel
theorem subd1_7_25 : subd1_7 [-1, 3] = true := by decide +kernel
theorem subd1_7_26 : subd1_7 [-1, 4] = true := by decide +kernel
theorem subd1_7_27 : subd1_7 [0, -5] = true := by decide +kernel
theorem subd1_7_28 : subd1_7 [0, -4] = true := by decide +kernel
theorem subd1_7_29 : subd1_7 [0, -3] = true := by decide +kernel
theorem subd1_7_30 : subd1_7 [0, -2] = true := by decide +kernel
theorem subd1_7_31 : subd1_7 [0, -1] = true := by decide +kernel
theorem sbd1_7_0 : ∀ q ∈ blkd1_7_0, subd1_7 q = true := by
  unfold blkd1_7_0
  exact List.forall_mem_cons.2 ⟨subd1_7_0, List.forall_mem_cons.2 ⟨subd1_7_1, List.forall_mem_cons.2 ⟨subd1_7_2, List.forall_mem_cons.2 ⟨subd1_7_3, List.forall_mem_cons.2 ⟨subd1_7_4, List.forall_mem_cons.2 ⟨subd1_7_5, List.forall_mem_cons.2 ⟨subd1_7_6, List.forall_mem_cons.2 ⟨subd1_7_7, List.forall_mem_cons.2 ⟨subd1_7_8, List.forall_mem_cons.2 ⟨subd1_7_9, List.forall_mem_cons.2 ⟨subd1_7_10, List.forall_mem_cons.2 ⟨subd1_7_11, List.forall_mem_cons.2 ⟨subd1_7_12, List.forall_mem_cons.2 ⟨subd1_7_13, List.forall_mem_cons.2 ⟨subd1_7_14, List.forall_mem_cons.2 ⟨subd1_7_15, List.forall_mem_cons.2 ⟨subd1_7_16, List.forall_mem_cons.2 ⟨subd1_7_17, List.forall_mem_cons.2 ⟨subd1_7_18, List.forall_mem_cons.2 ⟨subd1_7_19, List.forall_mem_cons.2 ⟨subd1_7_20, List.forall_mem_cons.2 ⟨subd1_7_21, List.forall_mem_cons.2 ⟨subd1_7_22, List.forall_mem_cons.2 ⟨subd1_7_23, List.forall_mem_cons.2 ⟨subd1_7_24, List.forall_mem_cons.2 ⟨subd1_7_25, List.forall_mem_cons.2 ⟨subd1_7_26, List.forall_mem_cons.2 ⟨subd1_7_27, List.forall_mem_cons.2 ⟨subd1_7_28, List.forall_mem_cons.2 ⟨subd1_7_29, List.forall_mem_cons.2 ⟨subd1_7_30, List.forall_mem_cons.2 ⟨subd1_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_7_32 : subd1_7 [0, 0] = true := by decide +kernel
theorem subd1_7_33 : subd1_7 [0, 1] = true := by decide +kernel
theorem subd1_7_34 : subd1_7 [0, 2] = true := by decide +kernel
theorem subd1_7_35 : subd1_7 [0, 3] = true := by decide +kernel
theorem subd1_7_36 : subd1_7 [0, 4] = true := by decide +kernel
theorem subd1_7_37 : subd1_7 [1, -5] = true := by decide +kernel
theorem subd1_7_38 : subd1_7 [1, -4] = true := by decide +kernel
theorem subd1_7_39 : subd1_7 [1, -3] = true := by decide +kernel
theorem subd1_7_40 : subd1_7 [1, -2] = true := by decide +kernel
theorem subd1_7_41 : subd1_7 [1, -1] = true := by decide +kernel
theorem subd1_7_42 : subd1_7 [1, 0] = true := by decide +kernel
theorem subd1_7_43 : subd1_7 [1, 1] = true := by decide +kernel
theorem subd1_7_44 : subd1_7 [1, 2] = true := by decide +kernel
theorem subd1_7_45 : subd1_7 [1, 3] = true := by decide +kernel
theorem subd1_7_46 : subd1_7 [1, 4] = true := by decide +kernel
theorem subd1_7_47 : subd1_7 [2, -4] = true := by decide +kernel
theorem subd1_7_48 : subd1_7 [2, -3] = true := by decide +kernel
theorem subd1_7_49 : subd1_7 [2, -2] = true := by decide +kernel
theorem subd1_7_50 : subd1_7 [2, -1] = true := by decide +kernel
theorem subd1_7_51 : subd1_7 [2, 0] = true := by decide +kernel
theorem subd1_7_52 : subd1_7 [2, 1] = true := by decide +kernel
theorem subd1_7_53 : subd1_7 [2, 2] = true := by decide +kernel
theorem subd1_7_54 : subd1_7 [2, 3] = true := by decide +kernel
theorem subd1_7_55 : subd1_7 [3, -4] = true := by decide +kernel
theorem subd1_7_56 : subd1_7 [3, -3] = true := by decide +kernel
theorem subd1_7_57 : subd1_7 [3, -2] = true := by decide +kernel
theorem subd1_7_58 : subd1_7 [3, -1] = true := by decide +kernel
theorem subd1_7_59 : subd1_7 [3, 0] = true := by decide +kernel
theorem subd1_7_60 : subd1_7 [3, 1] = true := by decide +kernel
theorem subd1_7_61 : subd1_7 [3, 2] = true := by decide +kernel
theorem subd1_7_62 : subd1_7 [3, 3] = true := by decide +kernel
theorem subd1_7_63 : subd1_7 [4] = true := by decide +kernel
theorem sbd1_7_1 : ∀ q ∈ blkd1_7_1, subd1_7 q = true := by
  unfold blkd1_7_1
  exact List.forall_mem_cons.2 ⟨subd1_7_32, List.forall_mem_cons.2 ⟨subd1_7_33, List.forall_mem_cons.2 ⟨subd1_7_34, List.forall_mem_cons.2 ⟨subd1_7_35, List.forall_mem_cons.2 ⟨subd1_7_36, List.forall_mem_cons.2 ⟨subd1_7_37, List.forall_mem_cons.2 ⟨subd1_7_38, List.forall_mem_cons.2 ⟨subd1_7_39, List.forall_mem_cons.2 ⟨subd1_7_40, List.forall_mem_cons.2 ⟨subd1_7_41, List.forall_mem_cons.2 ⟨subd1_7_42, List.forall_mem_cons.2 ⟨subd1_7_43, List.forall_mem_cons.2 ⟨subd1_7_44, List.forall_mem_cons.2 ⟨subd1_7_45, List.forall_mem_cons.2 ⟨subd1_7_46, List.forall_mem_cons.2 ⟨subd1_7_47, List.forall_mem_cons.2 ⟨subd1_7_48, List.forall_mem_cons.2 ⟨subd1_7_49, List.forall_mem_cons.2 ⟨subd1_7_50, List.forall_mem_cons.2 ⟨subd1_7_51, List.forall_mem_cons.2 ⟨subd1_7_52, List.forall_mem_cons.2 ⟨subd1_7_53, List.forall_mem_cons.2 ⟨subd1_7_54, List.forall_mem_cons.2 ⟨subd1_7_55, List.forall_mem_cons.2 ⟨subd1_7_56, List.forall_mem_cons.2 ⟨subd1_7_57, List.forall_mem_cons.2 ⟨subd1_7_58, List.forall_mem_cons.2 ⟨subd1_7_59, List.forall_mem_cons.2 ⟨subd1_7_60, List.forall_mem_cons.2 ⟨subd1_7_61, List.forall_mem_cons.2 ⟨subd1_7_62, List.forall_mem_cons.2 ⟨subd1_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
