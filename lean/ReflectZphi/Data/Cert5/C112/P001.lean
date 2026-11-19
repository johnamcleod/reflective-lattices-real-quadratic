import ReflectZphi.Data.Cert5.C112.Base

namespace ReflectZphi.Data.Cert5.C112

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd1_2_0 : subd1_2 [-4] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-3, -3] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [-3, -2] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [-3, -1] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [-3, 0] = true := by decide +kernel
theorem subd1_2_5 : subd1_2 [-3, 1] = true := by decide +kernel
theorem subd1_2_6 : subd1_2 [-3, 2] = true := by decide +kernel
theorem subd1_2_7 : subd1_2 [-3, 3] = true := by decide +kernel
theorem subd1_2_8 : subd1_2 [-3, 4] = true := by decide +kernel
theorem subd1_2_9 : subd1_2 [-2, -5] = true := by decide +kernel
theorem subd1_2_10 : subd1_2 [-2, -4] = true := by decide +kernel
theorem subd1_2_11 : subd1_2 [-2, -3] = true := by decide +kernel
theorem subd1_2_12 : subd1_2 [-2, -2] = true := by decide +kernel
theorem subd1_2_13 : subd1_2 [-2, -1] = true := by decide +kernel
theorem subd1_2_14 : subd1_2 [-2, 0] = true := by decide +kernel
theorem subd1_2_15 : subd1_2 [-2, 1] = true := by decide +kernel
theorem subd1_2_16 : subd1_2 [-2, 2] = true := by decide +kernel
theorem subd1_2_17 : subd1_2 [-2, 3] = true := by decide +kernel
theorem subd1_2_18 : subd1_2 [-2, 4] = true := by decide +kernel
theorem subd1_2_19 : subd1_2 [-2, 5] = true := by decide +kernel
theorem subd1_2_20 : subd1_2 [-1, -5] = true := by decide +kernel
theorem subd1_2_21 : subd1_2 [-1, -4] = true := by decide +kernel
theorem subd1_2_22 : subd1_2 [-1, -3] = true := by decide +kernel
theorem subd1_2_23 : subd1_2 [-1, -2] = true := by decide +kernel
theorem subd1_2_24 : subd1_2 [-1, -1] = true := by decide +kernel
theorem subd1_2_25 : subd1_2 [-1, 0] = true := by decide +kernel
theorem subd1_2_26 : subd1_2 [-1, 1] = true := by decide +kernel
theorem subd1_2_27 : subd1_2 [-1, 2] = true := by decide +kernel
theorem subd1_2_28 : subd1_2 [-1, 3] = true := by decide +kernel
theorem subd1_2_29 : subd1_2 [-1, 4] = true := by decide +kernel
theorem subd1_2_30 : subd1_2 [-1, 5] = true := by decide +kernel
theorem subd1_2_31 : subd1_2 [0, -6] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_cons.2 ⟨subd1_2_5, List.forall_mem_cons.2 ⟨subd1_2_6, List.forall_mem_cons.2 ⟨subd1_2_7, List.forall_mem_cons.2 ⟨subd1_2_8, List.forall_mem_cons.2 ⟨subd1_2_9, List.forall_mem_cons.2 ⟨subd1_2_10, List.forall_mem_cons.2 ⟨subd1_2_11, List.forall_mem_cons.2 ⟨subd1_2_12, List.forall_mem_cons.2 ⟨subd1_2_13, List.forall_mem_cons.2 ⟨subd1_2_14, List.forall_mem_cons.2 ⟨subd1_2_15, List.forall_mem_cons.2 ⟨subd1_2_16, List.forall_mem_cons.2 ⟨subd1_2_17, List.forall_mem_cons.2 ⟨subd1_2_18, List.forall_mem_cons.2 ⟨subd1_2_19, List.forall_mem_cons.2 ⟨subd1_2_20, List.forall_mem_cons.2 ⟨subd1_2_21, List.forall_mem_cons.2 ⟨subd1_2_22, List.forall_mem_cons.2 ⟨subd1_2_23, List.forall_mem_cons.2 ⟨subd1_2_24, List.forall_mem_cons.2 ⟨subd1_2_25, List.forall_mem_cons.2 ⟨subd1_2_26, List.forall_mem_cons.2 ⟨subd1_2_27, List.forall_mem_cons.2 ⟨subd1_2_28, List.forall_mem_cons.2 ⟨subd1_2_29, List.forall_mem_cons.2 ⟨subd1_2_30, List.forall_mem_cons.2 ⟨subd1_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_2_32 : subd1_2 [0, -5] = true := by decide +kernel
theorem subd1_2_33 : subd1_2 [0, -4] = true := by decide +kernel
theorem subd1_2_34 : subd1_2 [0, -3] = true := by decide +kernel
theorem subd1_2_35 : subd1_2 [0, -2] = true := by decide +kernel
theorem subd1_2_36 : subd1_2 [0, -1] = true := by decide +kernel
theorem subd1_2_37 : subd1_2 [0, 0] = true := by decide +kernel
theorem subd1_2_38 : subd1_2 [0, 1] = true := by decide +kernel
theorem subd1_2_39 : subd1_2 [0, 2] = true := by decide +kernel
theorem subd1_2_40 : subd1_2 [0, 3] = true := by decide +kernel
theorem subd1_2_41 : subd1_2 [0, 4] = true := by decide +kernel
theorem subd1_2_42 : subd1_2 [0, 5] = true := by decide +kernel
theorem subd1_2_43 : subd1_2 [1, -6] = true := by decide +kernel
theorem subd1_2_44 : subd1_2 [1, -5] = true := by decide +kernel
theorem subd1_2_45 : subd1_2 [1, -4] = true := by decide +kernel
theorem subd1_2_46 : subd1_2 [1, -3] = true := by decide +kernel
theorem subd1_2_47 : subd1_2 [1, -2] = true := by decide +kernel
theorem subd1_2_48 : subd1_2 [1, -1] = true := by decide +kernel
theorem subd1_2_49 : subd1_2 [1, 0] = true := by decide +kernel
theorem subd1_2_50 : subd1_2 [1, 1] = true := by decide +kernel
theorem subd1_2_51 : subd1_2 [1, 2] = true := by decide +kernel
theorem subd1_2_52 : subd1_2 [1, 3] = true := by decide +kernel
theorem subd1_2_53 : subd1_2 [1, 4] = true := by decide +kernel
theorem subd1_2_54 : subd1_2 [2, -6] = true := by decide +kernel
theorem subd1_2_55 : subd1_2 [2, -5] = true := by decide +kernel
theorem subd1_2_56 : subd1_2 [2, -4] = true := by decide +kernel
theorem subd1_2_57 : subd1_2 [2, -3] = true := by decide +kernel
theorem subd1_2_58 : subd1_2 [2, -2] = true := by decide +kernel
theorem subd1_2_59 : subd1_2 [2, -1] = true := by decide +kernel
theorem subd1_2_60 : subd1_2 [2, 0] = true := by decide +kernel
theorem subd1_2_61 : subd1_2 [2, 1] = true := by decide +kernel
theorem subd1_2_62 : subd1_2 [2, 2] = true := by decide +kernel
theorem subd1_2_63 : subd1_2 [2, 3] = true := by decide +kernel
theorem sbd1_2_1 : ∀ q ∈ blkd1_2_1, subd1_2 q = true := by
  unfold blkd1_2_1
  exact List.forall_mem_cons.2 ⟨subd1_2_32, List.forall_mem_cons.2 ⟨subd1_2_33, List.forall_mem_cons.2 ⟨subd1_2_34, List.forall_mem_cons.2 ⟨subd1_2_35, List.forall_mem_cons.2 ⟨subd1_2_36, List.forall_mem_cons.2 ⟨subd1_2_37, List.forall_mem_cons.2 ⟨subd1_2_38, List.forall_mem_cons.2 ⟨subd1_2_39, List.forall_mem_cons.2 ⟨subd1_2_40, List.forall_mem_cons.2 ⟨subd1_2_41, List.forall_mem_cons.2 ⟨subd1_2_42, List.forall_mem_cons.2 ⟨subd1_2_43, List.forall_mem_cons.2 ⟨subd1_2_44, List.forall_mem_cons.2 ⟨subd1_2_45, List.forall_mem_cons.2 ⟨subd1_2_46, List.forall_mem_cons.2 ⟨subd1_2_47, List.forall_mem_cons.2 ⟨subd1_2_48, List.forall_mem_cons.2 ⟨subd1_2_49, List.forall_mem_cons.2 ⟨subd1_2_50, List.forall_mem_cons.2 ⟨subd1_2_51, List.forall_mem_cons.2 ⟨subd1_2_52, List.forall_mem_cons.2 ⟨subd1_2_53, List.forall_mem_cons.2 ⟨subd1_2_54, List.forall_mem_cons.2 ⟨subd1_2_55, List.forall_mem_cons.2 ⟨subd1_2_56, List.forall_mem_cons.2 ⟨subd1_2_57, List.forall_mem_cons.2 ⟨subd1_2_58, List.forall_mem_cons.2 ⟨subd1_2_59, List.forall_mem_cons.2 ⟨subd1_2_60, List.forall_mem_cons.2 ⟨subd1_2_61, List.forall_mem_cons.2 ⟨subd1_2_62, List.forall_mem_cons.2 ⟨subd1_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd1_2_64 : subd1_2 [2, 4] = true := by decide +kernel
theorem subd1_2_65 : subd1_2 [3, -5] = true := by decide +kernel
theorem subd1_2_66 : subd1_2 [3, -4] = true := by decide +kernel
theorem subd1_2_67 : subd1_2 [3, -3] = true := by decide +kernel
theorem subd1_2_68 : subd1_2 [3, -2] = true := by decide +kernel
theorem subd1_2_69 : subd1_2 [3, -1] = true := by decide +kernel
theorem subd1_2_70 : subd1_2 [3, 0] = true := by decide +kernel
theorem subd1_2_71 : subd1_2 [3, 1] = true := by decide +kernel
theorem subd1_2_72 : subd1_2 [3, 2] = true := by decide +kernel
theorem subd1_2_73 : subd1_2 [4] = true := by decide +kernel
theorem sbd1_2_2 : ∀ q ∈ blkd1_2_2, subd1_2 q = true := by
  unfold blkd1_2_2
  exact List.forall_mem_cons.2 ⟨subd1_2_64, List.forall_mem_cons.2 ⟨subd1_2_65, List.forall_mem_cons.2 ⟨subd1_2_66, List.forall_mem_cons.2 ⟨subd1_2_67, List.forall_mem_cons.2 ⟨subd1_2_68, List.forall_mem_cons.2 ⟨subd1_2_69, List.forall_mem_cons.2 ⟨subd1_2_70, List.forall_mem_cons.2 ⟨subd1_2_71, List.forall_mem_cons.2 ⟨subd1_2_72, List.forall_mem_cons.2 ⟨subd1_2_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [-3] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [0, -3] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [0, -2] = true := by decide +kernel
theorem subd1_3_5 : subd1_3 [0, -1] = true := by decide +kernel
theorem subd1_3_6 : subd1_3 [0, 0] = true := by decide +kernel
theorem subd1_3_7 : subd1_3 [0, 1] = true := by decide +kernel
theorem subd1_3_8 : subd1_3 [0, 2] = true := by decide +kernel
theorem subd1_3_9 : subd1_3 [1] = true := by decide +kernel
theorem subd1_3_10 : subd1_3 [2] = true := by decide +kernel
theorem subd1_3_11 : subd1_3 [3] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_cons.2 ⟨subd1_3_5, List.forall_mem_cons.2 ⟨subd1_3_6, List.forall_mem_cons.2 ⟨subd1_3_7, List.forall_mem_cons.2 ⟨subd1_3_8, List.forall_mem_cons.2 ⟨subd1_3_9, List.forall_mem_cons.2 ⟨subd1_3_10, List.forall_mem_cons.2 ⟨subd1_3_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd1_4 : ldCheck G d1_4.U d1_4.ms ldd1_4 = true := by decide +kernel
theorem pre_okd1_4 : subPre G cell1 d1_4 = true := by decide +kernel
theorem subd1_4_0 : subd1_4 [-3] = true := by decide +kernel
theorem subd1_4_1 : subd1_4 [-2] = true := by decide +kernel
theorem subd1_4_2 : subd1_4 [-1, -5] = true := by decide +kernel
theorem subd1_4_3 : subd1_4 [-1, -4] = true := by decide +kernel
theorem subd1_4_4 : subd1_4 [-1, -3] = true := by decide +kernel
theorem subd1_4_5 : subd1_4 [-1, -2] = true := by decide +kernel
theorem subd1_4_6 : subd1_4 [-1, -1] = true := by decide +kernel
theorem subd1_4_7 : subd1_4 [-1, 0] = true := by decide +kernel
theorem subd1_4_8 : subd1_4 [-1, 1] = true := by decide +kernel
theorem subd1_4_9 : subd1_4 [-1, 2] = true := by decide +kernel
theorem subd1_4_10 : subd1_4 [-1, 3] = true := by decide +kernel
theorem subd1_4_11 : subd1_4 [0, -5] = true := by decide +kernel
theorem subd1_4_12 : subd1_4 [0, -4] = true := by decide +kernel
theorem subd1_4_13 : subd1_4 [0, -3] = true := by decide +kernel
theorem subd1_4_14 : subd1_4 [0, -2] = true := by decide +kernel
theorem subd1_4_15 : subd1_4 [0, -1] = true := by decide +kernel
theorem subd1_4_16 : subd1_4 [0, 0] = true := by decide +kernel
theorem subd1_4_17 : subd1_4 [0, 1] = true := by decide +kernel
theorem subd1_4_18 : subd1_4 [0, 2] = true := by decide +kernel
theorem subd1_4_19 : subd1_4 [0, 3] = true := by decide +kernel
theorem subd1_4_20 : subd1_4 [0, 4] = true := by decide +kernel
theorem subd1_4_21 : subd1_4 [1, -4] = true := by decide +kernel
theorem subd1_4_22 : subd1_4 [1, -3] = true := by decide +kernel
theorem subd1_4_23 : subd1_4 [1, -2] = true := by decide +kernel
theorem subd1_4_24 : subd1_4 [1, -1] = true := by decide +kernel
theorem subd1_4_25 : subd1_4 [1, 0] = true := by decide +kernel
theorem subd1_4_26 : subd1_4 [1, 1] = true := by decide +kernel
theorem subd1_4_27 : subd1_4 [1, 2] = true := by decide +kernel
theorem subd1_4_28 : subd1_4 [1, 3] = true := by decide +kernel
theorem subd1_4_29 : subd1_4 [1, 4] = true := by decide +kernel
theorem subd1_4_30 : subd1_4 [2] = true := by decide +kernel
theorem subd1_4_31 : subd1_4 [3] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_cons.2 ⟨subd1_4_1, List.forall_mem_cons.2 ⟨subd1_4_2, List.forall_mem_cons.2 ⟨subd1_4_3, List.forall_mem_cons.2 ⟨subd1_4_4, List.forall_mem_cons.2 ⟨subd1_4_5, List.forall_mem_cons.2 ⟨subd1_4_6, List.forall_mem_cons.2 ⟨subd1_4_7, List.forall_mem_cons.2 ⟨subd1_4_8, List.forall_mem_cons.2 ⟨subd1_4_9, List.forall_mem_cons.2 ⟨subd1_4_10, List.forall_mem_cons.2 ⟨subd1_4_11, List.forall_mem_cons.2 ⟨subd1_4_12, List.forall_mem_cons.2 ⟨subd1_4_13, List.forall_mem_cons.2 ⟨subd1_4_14, List.forall_mem_cons.2 ⟨subd1_4_15, List.forall_mem_cons.2 ⟨subd1_4_16, List.forall_mem_cons.2 ⟨subd1_4_17, List.forall_mem_cons.2 ⟨subd1_4_18, List.forall_mem_cons.2 ⟨subd1_4_19, List.forall_mem_cons.2 ⟨subd1_4_20, List.forall_mem_cons.2 ⟨subd1_4_21, List.forall_mem_cons.2 ⟨subd1_4_22, List.forall_mem_cons.2 ⟨subd1_4_23, List.forall_mem_cons.2 ⟨subd1_4_24, List.forall_mem_cons.2 ⟨subd1_4_25, List.forall_mem_cons.2 ⟨subd1_4_26, List.forall_mem_cons.2 ⟨subd1_4_27, List.forall_mem_cons.2 ⟨subd1_4_28, List.forall_mem_cons.2 ⟨subd1_4_29, List.forall_mem_cons.2 ⟨subd1_4_30, List.forall_mem_cons.2 ⟨subd1_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C112
