import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_3_0 : subd2_3 [-2] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [-1] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [0] = true := by decide +kernel
theorem subd2_3_3 : subd2_3 [1] = true := by decide +kernel
theorem subd2_3_4 : subd2_3 [2] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_cons.2 ⟨subd2_3_3, List.forall_mem_cons.2 ⟨subd2_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-1, 0, -7] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-1, 0, -6] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-1, 0, -5] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-1, 0, -4] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-1, 0, -3] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [-1, 0, -2] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [-1, 0, -1] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [-1, 0, 0] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [-1, 0, 1] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [-1, 0, 2] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [-1, 0, 3] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [-1, 0, 4] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [-1, 0, 5] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [-1, 0, 6] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [0, -1, -7] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [0, -1, -6] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [0, -1, -5] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [0, -1, -4] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [0, -1, -3] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [0, -1, -2] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [0, -1, -1] = true := by decide +kernel
theorem subd3_0_25 : subd3_0 [0, -1, 0] = true := by decide +kernel
theorem subd3_0_26 : subd3_0 [0, -1, 1] = true := by decide +kernel
theorem subd3_0_27 : subd3_0 [0, -1, 2] = true := by decide +kernel
theorem subd3_0_28 : subd3_0 [0, -1, 3] = true := by decide +kernel
theorem subd3_0_29 : subd3_0 [0, -1, 4] = true := by decide +kernel
theorem subd3_0_30 : subd3_0 [0, -1, 5] = true := by decide +kernel
theorem subd3_0_31 : subd3_0 [0, -1, 6] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_cons.2 ⟨subd3_0_25, List.forall_mem_cons.2 ⟨subd3_0_26, List.forall_mem_cons.2 ⟨subd3_0_27, List.forall_mem_cons.2 ⟨subd3_0_28, List.forall_mem_cons.2 ⟨subd3_0_29, List.forall_mem_cons.2 ⟨subd3_0_30, List.forall_mem_cons.2 ⟨subd3_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_32 : subd3_0 [0, -1, 7] = true := by decide +kernel
theorem subd3_0_33 : subd3_0 [0, 0, -8] = true := by decide +kernel
theorem subd3_0_34 : subd3_0 [0, 0, -7] = true := by decide +kernel
theorem subd3_0_35 : subd3_0 [0, 0, -6] = true := by decide +kernel
theorem subd3_0_36 : subd3_0 [0, 0, -5] = true := by decide +kernel
theorem subd3_0_37 : subd3_0 [0, 0, -4] = true := by decide +kernel
theorem subd3_0_38 : subd3_0 [0, 0, -3] = true := by decide +kernel
theorem subd3_0_39 : subd3_0 [0, 0, -2] = true := by decide +kernel
theorem subd3_0_40 : subd3_0 [0, 0, -1] = true := by decide +kernel
theorem subd3_0_41 : subd3_0 [0, 0, 0] = true := by decide +kernel
theorem subd3_0_42 : subd3_0 [0, 0, 1] = true := by decide +kernel
theorem subd3_0_43 : subd3_0 [0, 0, 2] = true := by decide +kernel
theorem subd3_0_44 : subd3_0 [0, 0, 3] = true := by decide +kernel
theorem subd3_0_45 : subd3_0 [0, 0, 4] = true := by decide +kernel
theorem subd3_0_46 : subd3_0 [0, 0, 5] = true := by decide +kernel
theorem subd3_0_47 : subd3_0 [0, 0, 6] = true := by decide +kernel
theorem subd3_0_48 : subd3_0 [0, 0, 7] = true := by decide +kernel
theorem subd3_0_49 : subd3_0 [0, 1, -8] = true := by decide +kernel
theorem subd3_0_50 : subd3_0 [0, 1, -7] = true := by decide +kernel
theorem subd3_0_51 : subd3_0 [0, 1, -6] = true := by decide +kernel
theorem subd3_0_52 : subd3_0 [0, 1, -5] = true := by decide +kernel
theorem subd3_0_53 : subd3_0 [0, 1, -4] = true := by decide +kernel
theorem subd3_0_54 : subd3_0 [0, 1, -3] = true := by decide +kernel
theorem subd3_0_55 : subd3_0 [0, 1, -2] = true := by decide +kernel
theorem subd3_0_56 : subd3_0 [0, 1, -1] = true := by decide +kernel
theorem subd3_0_57 : subd3_0 [0, 1, 0] = true := by decide +kernel
theorem subd3_0_58 : subd3_0 [0, 1, 1] = true := by decide +kernel
theorem subd3_0_59 : subd3_0 [0, 1, 2] = true := by decide +kernel
theorem subd3_0_60 : subd3_0 [0, 1, 3] = true := by decide +kernel
theorem subd3_0_61 : subd3_0 [0, 1, 4] = true := by decide +kernel
theorem subd3_0_62 : subd3_0 [0, 1, 5] = true := by decide +kernel
theorem subd3_0_63 : subd3_0 [0, 1, 6] = true := by decide +kernel
theorem sbd3_0_1 : ∀ q ∈ blkd3_0_1, subd3_0 q = true := by
  unfold blkd3_0_1
  exact List.forall_mem_cons.2 ⟨subd3_0_32, List.forall_mem_cons.2 ⟨subd3_0_33, List.forall_mem_cons.2 ⟨subd3_0_34, List.forall_mem_cons.2 ⟨subd3_0_35, List.forall_mem_cons.2 ⟨subd3_0_36, List.forall_mem_cons.2 ⟨subd3_0_37, List.forall_mem_cons.2 ⟨subd3_0_38, List.forall_mem_cons.2 ⟨subd3_0_39, List.forall_mem_cons.2 ⟨subd3_0_40, List.forall_mem_cons.2 ⟨subd3_0_41, List.forall_mem_cons.2 ⟨subd3_0_42, List.forall_mem_cons.2 ⟨subd3_0_43, List.forall_mem_cons.2 ⟨subd3_0_44, List.forall_mem_cons.2 ⟨subd3_0_45, List.forall_mem_cons.2 ⟨subd3_0_46, List.forall_mem_cons.2 ⟨subd3_0_47, List.forall_mem_cons.2 ⟨subd3_0_48, List.forall_mem_cons.2 ⟨subd3_0_49, List.forall_mem_cons.2 ⟨subd3_0_50, List.forall_mem_cons.2 ⟨subd3_0_51, List.forall_mem_cons.2 ⟨subd3_0_52, List.forall_mem_cons.2 ⟨subd3_0_53, List.forall_mem_cons.2 ⟨subd3_0_54, List.forall_mem_cons.2 ⟨subd3_0_55, List.forall_mem_cons.2 ⟨subd3_0_56, List.forall_mem_cons.2 ⟨subd3_0_57, List.forall_mem_cons.2 ⟨subd3_0_58, List.forall_mem_cons.2 ⟨subd3_0_59, List.forall_mem_cons.2 ⟨subd3_0_60, List.forall_mem_cons.2 ⟨subd3_0_61, List.forall_mem_cons.2 ⟨subd3_0_62, List.forall_mem_cons.2 ⟨subd3_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_64 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_65 : subd3_0 [1, -1] = true := by decide +kernel
theorem subd3_0_66 : subd3_0 [1, 0, -7] = true := by decide +kernel
theorem subd3_0_67 : subd3_0 [1, 0, -6] = true := by decide +kernel
theorem subd3_0_68 : subd3_0 [1, 0, -5] = true := by decide +kernel
theorem subd3_0_69 : subd3_0 [1, 0, -4] = true := by decide +kernel
theorem subd3_0_70 : subd3_0 [1, 0, -3] = true := by decide +kernel
theorem subd3_0_71 : subd3_0 [1, 0, -2] = true := by decide +kernel
theorem subd3_0_72 : subd3_0 [1, 0, -1] = true := by decide +kernel
theorem subd3_0_73 : subd3_0 [1, 0, 0] = true := by decide +kernel
theorem subd3_0_74 : subd3_0 [1, 0, 1] = true := by decide +kernel
theorem subd3_0_75 : subd3_0 [1, 0, 2] = true := by decide +kernel
theorem subd3_0_76 : subd3_0 [1, 0, 3] = true := by decide +kernel
theorem subd3_0_77 : subd3_0 [1, 0, 4] = true := by decide +kernel
theorem subd3_0_78 : subd3_0 [1, 0, 5] = true := by decide +kernel
theorem subd3_0_79 : subd3_0 [1, 0, 6] = true := by decide +kernel
theorem subd3_0_80 : subd3_0 [1, 1] = true := by decide +kernel
theorem sbd3_0_2 : ∀ q ∈ blkd3_0_2, subd3_0 q = true := by
  unfold blkd3_0_2
  exact List.forall_mem_cons.2 ⟨subd3_0_64, List.forall_mem_cons.2 ⟨subd3_0_65, List.forall_mem_cons.2 ⟨subd3_0_66, List.forall_mem_cons.2 ⟨subd3_0_67, List.forall_mem_cons.2 ⟨subd3_0_68, List.forall_mem_cons.2 ⟨subd3_0_69, List.forall_mem_cons.2 ⟨subd3_0_70, List.forall_mem_cons.2 ⟨subd3_0_71, List.forall_mem_cons.2 ⟨subd3_0_72, List.forall_mem_cons.2 ⟨subd3_0_73, List.forall_mem_cons.2 ⟨subd3_0_74, List.forall_mem_cons.2 ⟨subd3_0_75, List.forall_mem_cons.2 ⟨subd3_0_76, List.forall_mem_cons.2 ⟨subd3_0_77, List.forall_mem_cons.2 ⟨subd3_0_78, List.forall_mem_cons.2 ⟨subd3_0_79, List.forall_mem_cons.2 ⟨subd3_0_80, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩
theorem ld_okd3_3 : ldCheck G d3_3.U d3_3.ms ldd3_3 = true := by decide +kernel
theorem pre_okd3_3 : subPre G cell3 d3_3 = true := by decide +kernel
theorem subd3_3_0 : subd3_3 [] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_nil _⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel
theorem subd3_4_0 : subd3_4 [] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_nil _⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C093
