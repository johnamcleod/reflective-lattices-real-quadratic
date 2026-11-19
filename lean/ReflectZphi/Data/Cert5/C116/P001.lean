import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [0, -1] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [0, 0, -8] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [0, 0, -7] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [0, 0, -6] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [0, 0, -5] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [0, 0, -4] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [0, 0, -3] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [0, 0, -2] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [0, 0, -1] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [0, 0, 0] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [0, 0, 1] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [0, 0, 2] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [0, 0, 3] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [0, 0, 4] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [0, 0, 5] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [0, 0, 6] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [0, 0, 7] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-4] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-3, -6] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-3, -5] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-3, -4] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-3, -3] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-3, -2] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-3, -1] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [-3, 0] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [-3, 1] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [-3, 2] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [-2, -6] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [-2, -5] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [-2, -4] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [-2, -3] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [-2, -2] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [-2, -1] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [-2, 0] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [-2, 1] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [-2, 2] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [-2, 3] = true := by decide +kernel
theorem subd3_1_20 : subd3_1 [-1, -6] = true := by decide +kernel
theorem subd3_1_21 : subd3_1 [-1, -5] = true := by decide +kernel
theorem subd3_1_22 : subd3_1 [-1, -4] = true := by decide +kernel
theorem subd3_1_23 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_24 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_25 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_26 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_27 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_28 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_29 : subd3_1 [-1, 3] = true := by decide +kernel
theorem subd3_1_30 : subd3_1 [-1, 4] = true := by decide +kernel
theorem subd3_1_31 : subd3_1 [0, -6] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_cons.2 ⟨subd3_1_20, List.forall_mem_cons.2 ⟨subd3_1_21, List.forall_mem_cons.2 ⟨subd3_1_22, List.forall_mem_cons.2 ⟨subd3_1_23, List.forall_mem_cons.2 ⟨subd3_1_24, List.forall_mem_cons.2 ⟨subd3_1_25, List.forall_mem_cons.2 ⟨subd3_1_26, List.forall_mem_cons.2 ⟨subd3_1_27, List.forall_mem_cons.2 ⟨subd3_1_28, List.forall_mem_cons.2 ⟨subd3_1_29, List.forall_mem_cons.2 ⟨subd3_1_30, List.forall_mem_cons.2 ⟨subd3_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_32 : subd3_1 [0, -5] = true := by decide +kernel
theorem subd3_1_33 : subd3_1 [0, -4] = true := by decide +kernel
theorem subd3_1_34 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_35 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_36 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_37 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_38 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_39 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_40 : subd3_1 [0, 3] = true := by decide +kernel
theorem subd3_1_41 : subd3_1 [0, 4] = true := by decide +kernel
theorem subd3_1_42 : subd3_1 [0, 5] = true := by decide +kernel
theorem subd3_1_43 : subd3_1 [1, -5] = true := by decide +kernel
theorem subd3_1_44 : subd3_1 [1, -4] = true := by decide +kernel
theorem subd3_1_45 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_46 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_47 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_48 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_49 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_50 : subd3_1 [1, 2] = true := by decide +kernel
theorem subd3_1_51 : subd3_1 [1, 3] = true := by decide +kernel
theorem subd3_1_52 : subd3_1 [1, 4] = true := by decide +kernel
theorem subd3_1_53 : subd3_1 [1, 5] = true := by decide +kernel
theorem subd3_1_54 : subd3_1 [2, -4] = true := by decide +kernel
theorem subd3_1_55 : subd3_1 [2, -3] = true := by decide +kernel
theorem subd3_1_56 : subd3_1 [2, -2] = true := by decide +kernel
theorem subd3_1_57 : subd3_1 [2, -1] = true := by decide +kernel
theorem subd3_1_58 : subd3_1 [2, 0] = true := by decide +kernel
theorem subd3_1_59 : subd3_1 [2, 1] = true := by decide +kernel
theorem subd3_1_60 : subd3_1 [2, 2] = true := by decide +kernel
theorem subd3_1_61 : subd3_1 [2, 3] = true := by decide +kernel
theorem subd3_1_62 : subd3_1 [2, 4] = true := by decide +kernel
theorem subd3_1_63 : subd3_1 [2, 5] = true := by decide +kernel
theorem sbd3_1_1 : ∀ q ∈ blkd3_1_1, subd3_1 q = true := by
  unfold blkd3_1_1
  exact List.forall_mem_cons.2 ⟨subd3_1_32, List.forall_mem_cons.2 ⟨subd3_1_33, List.forall_mem_cons.2 ⟨subd3_1_34, List.forall_mem_cons.2 ⟨subd3_1_35, List.forall_mem_cons.2 ⟨subd3_1_36, List.forall_mem_cons.2 ⟨subd3_1_37, List.forall_mem_cons.2 ⟨subd3_1_38, List.forall_mem_cons.2 ⟨subd3_1_39, List.forall_mem_cons.2 ⟨subd3_1_40, List.forall_mem_cons.2 ⟨subd3_1_41, List.forall_mem_cons.2 ⟨subd3_1_42, List.forall_mem_cons.2 ⟨subd3_1_43, List.forall_mem_cons.2 ⟨subd3_1_44, List.forall_mem_cons.2 ⟨subd3_1_45, List.forall_mem_cons.2 ⟨subd3_1_46, List.forall_mem_cons.2 ⟨subd3_1_47, List.forall_mem_cons.2 ⟨subd3_1_48, List.forall_mem_cons.2 ⟨subd3_1_49, List.forall_mem_cons.2 ⟨subd3_1_50, List.forall_mem_cons.2 ⟨subd3_1_51, List.forall_mem_cons.2 ⟨subd3_1_52, List.forall_mem_cons.2 ⟨subd3_1_53, List.forall_mem_cons.2 ⟨subd3_1_54, List.forall_mem_cons.2 ⟨subd3_1_55, List.forall_mem_cons.2 ⟨subd3_1_56, List.forall_mem_cons.2 ⟨subd3_1_57, List.forall_mem_cons.2 ⟨subd3_1_58, List.forall_mem_cons.2 ⟨subd3_1_59, List.forall_mem_cons.2 ⟨subd3_1_60, List.forall_mem_cons.2 ⟨subd3_1_61, List.forall_mem_cons.2 ⟨subd3_1_62, List.forall_mem_cons.2 ⟨subd3_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_1_64 : subd3_1 [3, -3] = true := by decide +kernel
theorem subd3_1_65 : subd3_1 [3, -2] = true := by decide +kernel
theorem subd3_1_66 : subd3_1 [3, -1] = true := by decide +kernel
theorem subd3_1_67 : subd3_1 [3, 0] = true := by decide +kernel
theorem subd3_1_68 : subd3_1 [3, 1] = true := by decide +kernel
theorem subd3_1_69 : subd3_1 [3, 2] = true := by decide +kernel
theorem subd3_1_70 : subd3_1 [3, 3] = true := by decide +kernel
theorem subd3_1_71 : subd3_1 [3, 4] = true := by decide +kernel
theorem subd3_1_72 : subd3_1 [3, 5] = true := by decide +kernel
theorem subd3_1_73 : subd3_1 [4] = true := by decide +kernel
theorem sbd3_1_2 : ∀ q ∈ blkd3_1_2, subd3_1 q = true := by
  unfold blkd3_1_2
  exact List.forall_mem_cons.2 ⟨subd3_1_64, List.forall_mem_cons.2 ⟨subd3_1_65, List.forall_mem_cons.2 ⟨subd3_1_66, List.forall_mem_cons.2 ⟨subd3_1_67, List.forall_mem_cons.2 ⟨subd3_1_68, List.forall_mem_cons.2 ⟨subd3_1_69, List.forall_mem_cons.2 ⟨subd3_1_70, List.forall_mem_cons.2 ⟨subd3_1_71, List.forall_mem_cons.2 ⟨subd3_1_72, List.forall_mem_cons.2 ⟨subd3_1_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [0, 0, -9] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [0, 0, -8] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [0, 0, -7] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [0, 0, -6] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [0, 0, -5] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [0, 0, -4] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [0, 0, -3] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [0, 0, -2] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [0, 0, -1] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [0, 0, 0] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [0, 0, 1] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [0, 0, 2] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [0, 0, 3] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [0, 0, 4] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [0, 0, 5] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [0, 0, 6] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [0, 0, 7] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [0, 0, 8] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
