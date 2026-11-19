import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-3] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-2] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-1, -4] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [-1, 3] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [0, -4] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [0, 3] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [1, -4] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_20 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_21 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_22 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_23 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_24 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_25 : subd3_2 [1, 3] = true := by decide +kernel
theorem subd3_2_26 : subd3_2 [2] = true := by decide +kernel
theorem subd3_2_27 : subd3_2 [3] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_cons.2 ⟨subd3_2_20, List.forall_mem_cons.2 ⟨subd3_2_21, List.forall_mem_cons.2 ⟨subd3_2_22, List.forall_mem_cons.2 ⟨subd3_2_23, List.forall_mem_cons.2 ⟨subd3_2_24, List.forall_mem_cons.2 ⟨subd3_2_25, List.forall_mem_cons.2 ⟨subd3_2_26, List.forall_mem_cons.2 ⟨subd3_2_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [-2] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-1] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [0] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [1] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [2] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [-3, -4] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-3, -3] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-3, -2] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-3, -1] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-3, 0] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-3, 1] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-2, -5] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-2, -4] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-2, -3] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [-2, -2] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [-2, -1] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [-2, 0] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [-2, 1] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [-2, 2] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [-1, -5] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [-1, -4] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [-1, -3] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [-1, -1] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [-1, 0] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [-1, 1] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [-1, 2] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [-1, 3] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [0, -5] = true := by decide +kernel
theorem subd3_4_24 : subd3_4 [0, -4] = true := by decide +kernel
theorem subd3_4_25 : subd3_4 [0, -3] = true := by decide +kernel
theorem subd3_4_26 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_27 : subd3_4 [0, -1] = true := by decide +kernel
theorem subd3_4_28 : subd3_4 [0, 0, -7] = true := by decide +kernel
theorem subd3_4_29 : subd3_4 [0, 0, -6] = true := by decide +kernel
theorem subd3_4_30 : subd3_4 [0, 0, -5] = true := by decide +kernel
theorem subd3_4_31 : subd3_4 [0, 0, -4] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_cons.2 ⟨subd3_4_24, List.forall_mem_cons.2 ⟨subd3_4_25, List.forall_mem_cons.2 ⟨subd3_4_26, List.forall_mem_cons.2 ⟨subd3_4_27, List.forall_mem_cons.2 ⟨subd3_4_28, List.forall_mem_cons.2 ⟨subd3_4_29, List.forall_mem_cons.2 ⟨subd3_4_30, List.forall_mem_cons.2 ⟨subd3_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_32 : subd3_4 [0, 0, -3] = true := by decide +kernel
theorem subd3_4_33 : subd3_4 [0, 0, -2] = true := by decide +kernel
theorem subd3_4_34 : subd3_4 [0, 0, -1] = true := by decide +kernel
theorem subd3_4_35 : subd3_4 [0, 0, 0] = true := by decide +kernel
theorem subd3_4_36 : subd3_4 [0, 0, 1] = true := by decide +kernel
theorem subd3_4_37 : subd3_4 [0, 0, 2] = true := by decide +kernel
theorem subd3_4_38 : subd3_4 [0, 0, 3] = true := by decide +kernel
theorem subd3_4_39 : subd3_4 [0, 0, 4] = true := by decide +kernel
theorem subd3_4_40 : subd3_4 [0, 0, 5] = true := by decide +kernel
theorem subd3_4_41 : subd3_4 [0, 0, 6] = true := by decide +kernel
theorem subd3_4_42 : subd3_4 [0, 1] = true := by decide +kernel
theorem subd3_4_43 : subd3_4 [0, 2] = true := by decide +kernel
theorem subd3_4_44 : subd3_4 [0, 3] = true := by decide +kernel
theorem subd3_4_45 : subd3_4 [0, 4] = true := by decide +kernel
theorem subd3_4_46 : subd3_4 [1, -4] = true := by decide +kernel
theorem subd3_4_47 : subd3_4 [1, -3] = true := by decide +kernel
theorem subd3_4_48 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_49 : subd3_4 [1, -1] = true := by decide +kernel
theorem subd3_4_50 : subd3_4 [1, 0] = true := by decide +kernel
theorem subd3_4_51 : subd3_4 [1, 1] = true := by decide +kernel
theorem subd3_4_52 : subd3_4 [1, 2] = true := by decide +kernel
theorem subd3_4_53 : subd3_4 [1, 3] = true := by decide +kernel
theorem subd3_4_54 : subd3_4 [1, 4] = true := by decide +kernel
theorem subd3_4_55 : subd3_4 [2, -3] = true := by decide +kernel
theorem subd3_4_56 : subd3_4 [2, -2] = true := by decide +kernel
theorem subd3_4_57 : subd3_4 [2, -1] = true := by decide +kernel
theorem subd3_4_58 : subd3_4 [2, 0] = true := by decide +kernel
theorem subd3_4_59 : subd3_4 [2, 1] = true := by decide +kernel
theorem subd3_4_60 : subd3_4 [2, 2] = true := by decide +kernel
theorem subd3_4_61 : subd3_4 [2, 3] = true := by decide +kernel
theorem subd3_4_62 : subd3_4 [2, 4] = true := by decide +kernel
theorem subd3_4_63 : subd3_4 [3, -2] = true := by decide +kernel
theorem sbd3_4_1 : ∀ q ∈ blkd3_4_1, subd3_4 q = true := by
  unfold blkd3_4_1
  exact List.forall_mem_cons.2 ⟨subd3_4_32, List.forall_mem_cons.2 ⟨subd3_4_33, List.forall_mem_cons.2 ⟨subd3_4_34, List.forall_mem_cons.2 ⟨subd3_4_35, List.forall_mem_cons.2 ⟨subd3_4_36, List.forall_mem_cons.2 ⟨subd3_4_37, List.forall_mem_cons.2 ⟨subd3_4_38, List.forall_mem_cons.2 ⟨subd3_4_39, List.forall_mem_cons.2 ⟨subd3_4_40, List.forall_mem_cons.2 ⟨subd3_4_41, List.forall_mem_cons.2 ⟨subd3_4_42, List.forall_mem_cons.2 ⟨subd3_4_43, List.forall_mem_cons.2 ⟨subd3_4_44, List.forall_mem_cons.2 ⟨subd3_4_45, List.forall_mem_cons.2 ⟨subd3_4_46, List.forall_mem_cons.2 ⟨subd3_4_47, List.forall_mem_cons.2 ⟨subd3_4_48, List.forall_mem_cons.2 ⟨subd3_4_49, List.forall_mem_cons.2 ⟨subd3_4_50, List.forall_mem_cons.2 ⟨subd3_4_51, List.forall_mem_cons.2 ⟨subd3_4_52, List.forall_mem_cons.2 ⟨subd3_4_53, List.forall_mem_cons.2 ⟨subd3_4_54, List.forall_mem_cons.2 ⟨subd3_4_55, List.forall_mem_cons.2 ⟨subd3_4_56, List.forall_mem_cons.2 ⟨subd3_4_57, List.forall_mem_cons.2 ⟨subd3_4_58, List.forall_mem_cons.2 ⟨subd3_4_59, List.forall_mem_cons.2 ⟨subd3_4_60, List.forall_mem_cons.2 ⟨subd3_4_61, List.forall_mem_cons.2 ⟨subd3_4_62, List.forall_mem_cons.2 ⟨subd3_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_4_64 : subd3_4 [3, -1] = true := by decide +kernel
theorem subd3_4_65 : subd3_4 [3, 0] = true := by decide +kernel
theorem subd3_4_66 : subd3_4 [3, 1] = true := by decide +kernel
theorem subd3_4_67 : subd3_4 [3, 2] = true := by decide +kernel
theorem subd3_4_68 : subd3_4 [3, 3] = true := by decide +kernel
theorem sbd3_4_2 : ∀ q ∈ blkd3_4_2, subd3_4 q = true := by
  unfold blkd3_4_2
  exact List.forall_mem_cons.2 ⟨subd3_4_64, List.forall_mem_cons.2 ⟨subd3_4_65, List.forall_mem_cons.2 ⟨subd3_4_66, List.forall_mem_cons.2 ⟨subd3_4_67, List.forall_mem_cons.2 ⟨subd3_4_68, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C123
