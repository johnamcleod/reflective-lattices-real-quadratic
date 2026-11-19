import ReflectZphi.Data.Cert5.C112.Base

namespace ReflectZphi.Data.Cert5.C112

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-4] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-3, -5] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-3, -4] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-3, -3] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-3, -2] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-3, -1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-3, 0] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [-3, 1] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [-3, 2] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [-2, -5] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [-2, -4] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [-2, -3] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [-2, -2] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [-2, -1] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [-2, 0] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [-2, 1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [-2, 2] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [-2, 3] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [-1, -5] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [-1, -4] = true := by decide +kernel
theorem subd3_2_20 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_21 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_22 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_23 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_24 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_25 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_26 : subd3_2 [-1, 3] = true := by decide +kernel
theorem subd3_2_27 : subd3_2 [0, -5] = true := by decide +kernel
theorem subd3_2_28 : subd3_2 [0, -4] = true := by decide +kernel
theorem subd3_2_29 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_30 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_31 : subd3_2 [0, -1] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_cons.2 ⟨subd3_2_20, List.forall_mem_cons.2 ⟨subd3_2_21, List.forall_mem_cons.2 ⟨subd3_2_22, List.forall_mem_cons.2 ⟨subd3_2_23, List.forall_mem_cons.2 ⟨subd3_2_24, List.forall_mem_cons.2 ⟨subd3_2_25, List.forall_mem_cons.2 ⟨subd3_2_26, List.forall_mem_cons.2 ⟨subd3_2_27, List.forall_mem_cons.2 ⟨subd3_2_28, List.forall_mem_cons.2 ⟨subd3_2_29, List.forall_mem_cons.2 ⟨subd3_2_30, List.forall_mem_cons.2 ⟨subd3_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_2_32 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_33 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_34 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_35 : subd3_2 [0, 3] = true := by decide +kernel
theorem subd3_2_36 : subd3_2 [0, 4] = true := by decide +kernel
theorem subd3_2_37 : subd3_2 [1, -4] = true := by decide +kernel
theorem subd3_2_38 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_39 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_40 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_41 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_42 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_43 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_44 : subd3_2 [1, 3] = true := by decide +kernel
theorem subd3_2_45 : subd3_2 [1, 4] = true := by decide +kernel
theorem subd3_2_46 : subd3_2 [2, -4] = true := by decide +kernel
theorem subd3_2_47 : subd3_2 [2, -3] = true := by decide +kernel
theorem subd3_2_48 : subd3_2 [2, -2] = true := by decide +kernel
theorem subd3_2_49 : subd3_2 [2, -1] = true := by decide +kernel
theorem subd3_2_50 : subd3_2 [2, 0] = true := by decide +kernel
theorem subd3_2_51 : subd3_2 [2, 1] = true := by decide +kernel
theorem subd3_2_52 : subd3_2 [2, 2] = true := by decide +kernel
theorem subd3_2_53 : subd3_2 [2, 3] = true := by decide +kernel
theorem subd3_2_54 : subd3_2 [2, 4] = true := by decide +kernel
theorem subd3_2_55 : subd3_2 [3, -3] = true := by decide +kernel
theorem subd3_2_56 : subd3_2 [3, -2] = true := by decide +kernel
theorem subd3_2_57 : subd3_2 [3, -1] = true := by decide +kernel
theorem subd3_2_58 : subd3_2 [3, 0] = true := by decide +kernel
theorem subd3_2_59 : subd3_2 [3, 1] = true := by decide +kernel
theorem subd3_2_60 : subd3_2 [3, 2] = true := by decide +kernel
theorem subd3_2_61 : subd3_2 [3, 3] = true := by decide +kernel
theorem subd3_2_62 : subd3_2 [3, 4] = true := by decide +kernel
theorem subd3_2_63 : subd3_2 [4] = true := by decide +kernel
theorem sbd3_2_1 : ∀ q ∈ blkd3_2_1, subd3_2 q = true := by
  unfold blkd3_2_1
  exact List.forall_mem_cons.2 ⟨subd3_2_32, List.forall_mem_cons.2 ⟨subd3_2_33, List.forall_mem_cons.2 ⟨subd3_2_34, List.forall_mem_cons.2 ⟨subd3_2_35, List.forall_mem_cons.2 ⟨subd3_2_36, List.forall_mem_cons.2 ⟨subd3_2_37, List.forall_mem_cons.2 ⟨subd3_2_38, List.forall_mem_cons.2 ⟨subd3_2_39, List.forall_mem_cons.2 ⟨subd3_2_40, List.forall_mem_cons.2 ⟨subd3_2_41, List.forall_mem_cons.2 ⟨subd3_2_42, List.forall_mem_cons.2 ⟨subd3_2_43, List.forall_mem_cons.2 ⟨subd3_2_44, List.forall_mem_cons.2 ⟨subd3_2_45, List.forall_mem_cons.2 ⟨subd3_2_46, List.forall_mem_cons.2 ⟨subd3_2_47, List.forall_mem_cons.2 ⟨subd3_2_48, List.forall_mem_cons.2 ⟨subd3_2_49, List.forall_mem_cons.2 ⟨subd3_2_50, List.forall_mem_cons.2 ⟨subd3_2_51, List.forall_mem_cons.2 ⟨subd3_2_52, List.forall_mem_cons.2 ⟨subd3_2_53, List.forall_mem_cons.2 ⟨subd3_2_54, List.forall_mem_cons.2 ⟨subd3_2_55, List.forall_mem_cons.2 ⟨subd3_2_56, List.forall_mem_cons.2 ⟨subd3_2_57, List.forall_mem_cons.2 ⟨subd3_2_58, List.forall_mem_cons.2 ⟨subd3_2_59, List.forall_mem_cons.2 ⟨subd3_2_60, List.forall_mem_cons.2 ⟨subd3_2_61, List.forall_mem_cons.2 ⟨subd3_2_62, List.forall_mem_cons.2 ⟨subd3_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem subd3_4_0 : subd3_4 [-3] = true := by decide +kernel
theorem subd3_4_1 : subd3_4 [-2] = true := by decide +kernel
theorem subd3_4_2 : subd3_4 [-1, -4] = true := by decide +kernel
theorem subd3_4_3 : subd3_4 [-1, -3] = true := by decide +kernel
theorem subd3_4_4 : subd3_4 [-1, -2] = true := by decide +kernel
theorem subd3_4_5 : subd3_4 [-1, -1] = true := by decide +kernel
theorem subd3_4_6 : subd3_4 [-1, 0] = true := by decide +kernel
theorem subd3_4_7 : subd3_4 [-1, 1] = true := by decide +kernel
theorem subd3_4_8 : subd3_4 [-1, 2] = true := by decide +kernel
theorem subd3_4_9 : subd3_4 [0, -3] = true := by decide +kernel
theorem subd3_4_10 : subd3_4 [0, -2] = true := by decide +kernel
theorem subd3_4_11 : subd3_4 [0, -1] = true := by decide +kernel
theorem subd3_4_12 : subd3_4 [0, 0] = true := by decide +kernel
theorem subd3_4_13 : subd3_4 [0, 1] = true := by decide +kernel
theorem subd3_4_14 : subd3_4 [0, 2] = true := by decide +kernel
theorem subd3_4_15 : subd3_4 [1, -3] = true := by decide +kernel
theorem subd3_4_16 : subd3_4 [1, -2] = true := by decide +kernel
theorem subd3_4_17 : subd3_4 [1, -1] = true := by decide +kernel
theorem subd3_4_18 : subd3_4 [1, 0] = true := by decide +kernel
theorem subd3_4_19 : subd3_4 [1, 1] = true := by decide +kernel
theorem subd3_4_20 : subd3_4 [1, 2] = true := by decide +kernel
theorem subd3_4_21 : subd3_4 [1, 3] = true := by decide +kernel
theorem subd3_4_22 : subd3_4 [2] = true := by decide +kernel
theorem subd3_4_23 : subd3_4 [3] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_cons.2 ⟨subd3_4_1, List.forall_mem_cons.2 ⟨subd3_4_2, List.forall_mem_cons.2 ⟨subd3_4_3, List.forall_mem_cons.2 ⟨subd3_4_4, List.forall_mem_cons.2 ⟨subd3_4_5, List.forall_mem_cons.2 ⟨subd3_4_6, List.forall_mem_cons.2 ⟨subd3_4_7, List.forall_mem_cons.2 ⟨subd3_4_8, List.forall_mem_cons.2 ⟨subd3_4_9, List.forall_mem_cons.2 ⟨subd3_4_10, List.forall_mem_cons.2 ⟨subd3_4_11, List.forall_mem_cons.2 ⟨subd3_4_12, List.forall_mem_cons.2 ⟨subd3_4_13, List.forall_mem_cons.2 ⟨subd3_4_14, List.forall_mem_cons.2 ⟨subd3_4_15, List.forall_mem_cons.2 ⟨subd3_4_16, List.forall_mem_cons.2 ⟨subd3_4_17, List.forall_mem_cons.2 ⟨subd3_4_18, List.forall_mem_cons.2 ⟨subd3_4_19, List.forall_mem_cons.2 ⟨subd3_4_20, List.forall_mem_cons.2 ⟨subd3_4_21, List.forall_mem_cons.2 ⟨subd3_4_22, List.forall_mem_cons.2 ⟨subd3_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_nil _⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C112
