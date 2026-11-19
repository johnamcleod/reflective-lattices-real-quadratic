import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_32 : subd6_0 [-1, 2] = true := by decide +kernel
theorem subd6_0_33 : subd6_0 [-1, 3] = true := by decide +kernel
theorem subd6_0_34 : subd6_0 [-1, 4] = true := by decide +kernel
theorem subd6_0_35 : subd6_0 [0, -5] = true := by decide +kernel
theorem subd6_0_36 : subd6_0 [0, -4] = true := by decide +kernel
theorem subd6_0_37 : subd6_0 [0, -3] = true := by decide +kernel
theorem subd6_0_38 : subd6_0 [0, -2] = true := by decide +kernel
theorem subd6_0_39 : subd6_0 [0, -1] = true := by decide +kernel
theorem subd6_0_40 : subd6_0 [0, 0] = true := by decide +kernel
theorem subd6_0_41 : subd6_0 [0, 1] = true := by decide +kernel
theorem subd6_0_42 : subd6_0 [0, 2] = true := by decide +kernel
theorem subd6_0_43 : subd6_0 [0, 3] = true := by decide +kernel
theorem subd6_0_44 : subd6_0 [0, 4] = true := by decide +kernel
theorem subd6_0_45 : subd6_0 [1, -5] = true := by decide +kernel
theorem subd6_0_46 : subd6_0 [1, -4] = true := by decide +kernel
theorem subd6_0_47 : subd6_0 [1, -3] = true := by decide +kernel
theorem subd6_0_48 : subd6_0 [1, -2] = true := by decide +kernel
theorem subd6_0_49 : subd6_0 [1, -1] = true := by decide +kernel
theorem subd6_0_50 : subd6_0 [1, 0] = true := by decide +kernel
theorem subd6_0_51 : subd6_0 [1, 1] = true := by decide +kernel
theorem subd6_0_52 : subd6_0 [1, 2] = true := by decide +kernel
theorem subd6_0_53 : subd6_0 [1, 3] = true := by decide +kernel
theorem subd6_0_54 : subd6_0 [1, 4] = true := by decide +kernel
theorem subd6_0_55 : subd6_0 [2, -4] = true := by decide +kernel
theorem subd6_0_56 : subd6_0 [2, -3] = true := by decide +kernel
theorem subd6_0_57 : subd6_0 [2, -2] = true := by decide +kernel
theorem subd6_0_58 : subd6_0 [2, -1] = true := by decide +kernel
theorem subd6_0_59 : subd6_0 [2, 0] = true := by decide +kernel
theorem subd6_0_60 : subd6_0 [2, 1] = true := by decide +kernel
theorem subd6_0_61 : subd6_0 [2, 2] = true := by decide +kernel
theorem subd6_0_62 : subd6_0 [2, 3] = true := by decide +kernel
theorem subd6_0_63 : subd6_0 [2, 4] = true := by decide +kernel
theorem sbd6_0_1 : ∀ q ∈ blkd6_0_1, subd6_0 q = true := by
  unfold blkd6_0_1
  exact List.forall_mem_cons.2 ⟨subd6_0_32, List.forall_mem_cons.2 ⟨subd6_0_33, List.forall_mem_cons.2 ⟨subd6_0_34, List.forall_mem_cons.2 ⟨subd6_0_35, List.forall_mem_cons.2 ⟨subd6_0_36, List.forall_mem_cons.2 ⟨subd6_0_37, List.forall_mem_cons.2 ⟨subd6_0_38, List.forall_mem_cons.2 ⟨subd6_0_39, List.forall_mem_cons.2 ⟨subd6_0_40, List.forall_mem_cons.2 ⟨subd6_0_41, List.forall_mem_cons.2 ⟨subd6_0_42, List.forall_mem_cons.2 ⟨subd6_0_43, List.forall_mem_cons.2 ⟨subd6_0_44, List.forall_mem_cons.2 ⟨subd6_0_45, List.forall_mem_cons.2 ⟨subd6_0_46, List.forall_mem_cons.2 ⟨subd6_0_47, List.forall_mem_cons.2 ⟨subd6_0_48, List.forall_mem_cons.2 ⟨subd6_0_49, List.forall_mem_cons.2 ⟨subd6_0_50, List.forall_mem_cons.2 ⟨subd6_0_51, List.forall_mem_cons.2 ⟨subd6_0_52, List.forall_mem_cons.2 ⟨subd6_0_53, List.forall_mem_cons.2 ⟨subd6_0_54, List.forall_mem_cons.2 ⟨subd6_0_55, List.forall_mem_cons.2 ⟨subd6_0_56, List.forall_mem_cons.2 ⟨subd6_0_57, List.forall_mem_cons.2 ⟨subd6_0_58, List.forall_mem_cons.2 ⟨subd6_0_59, List.forall_mem_cons.2 ⟨subd6_0_60, List.forall_mem_cons.2 ⟨subd6_0_61, List.forall_mem_cons.2 ⟨subd6_0_62, List.forall_mem_cons.2 ⟨subd6_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_64 : subd6_0 [3, -3] = true := by decide +kernel
theorem subd6_0_65 : subd6_0 [3, -2] = true := by decide +kernel
theorem subd6_0_66 : subd6_0 [3, -1] = true := by decide +kernel
theorem subd6_0_67 : subd6_0 [3, 0] = true := by decide +kernel
theorem subd6_0_68 : subd6_0 [3, 1] = true := by decide +kernel
theorem subd6_0_69 : subd6_0 [3, 2] = true := by decide +kernel
theorem subd6_0_70 : subd6_0 [3, 3] = true := by decide +kernel
theorem subd6_0_71 : subd6_0 [3, 4] = true := by decide +kernel
theorem subd6_0_72 : subd6_0 [4, -2] = true := by decide +kernel
theorem subd6_0_73 : subd6_0 [4, -1] = true := by decide +kernel
theorem subd6_0_74 : subd6_0 [4, 0] = true := by decide +kernel
theorem subd6_0_75 : subd6_0 [4, 1] = true := by decide +kernel
theorem subd6_0_76 : subd6_0 [4, 2] = true := by decide +kernel
theorem subd6_0_77 : subd6_0 [4, 3] = true := by decide +kernel
theorem subd6_0_78 : subd6_0 [4, 4] = true := by decide +kernel
theorem subd6_0_79 : subd6_0 [5] = true := by decide +kernel
theorem sbd6_0_2 : ∀ q ∈ blkd6_0_2, subd6_0 q = true := by
  unfold blkd6_0_2
  exact List.forall_mem_cons.2 ⟨subd6_0_64, List.forall_mem_cons.2 ⟨subd6_0_65, List.forall_mem_cons.2 ⟨subd6_0_66, List.forall_mem_cons.2 ⟨subd6_0_67, List.forall_mem_cons.2 ⟨subd6_0_68, List.forall_mem_cons.2 ⟨subd6_0_69, List.forall_mem_cons.2 ⟨subd6_0_70, List.forall_mem_cons.2 ⟨subd6_0_71, List.forall_mem_cons.2 ⟨subd6_0_72, List.forall_mem_cons.2 ⟨subd6_0_73, List.forall_mem_cons.2 ⟨subd6_0_74, List.forall_mem_cons.2 ⟨subd6_0_75, List.forall_mem_cons.2 ⟨subd6_0_76, List.forall_mem_cons.2 ⟨subd6_0_77, List.forall_mem_cons.2 ⟨subd6_0_78, List.forall_mem_cons.2 ⟨subd6_0_79, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-3] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-2] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [0, 3] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [1, -4] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [1, -3] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [1, -2] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [1, -1] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [1, 0] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [1, 1] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [1, 2] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [1, 3] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [2] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [3] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-5] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-4] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-3, -3] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-3, -2] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-3, -1] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-3, 0] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-3, 1] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-3, 2] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-3, 3] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-3, 4] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [-3, 5] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [-2, -4] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [-2, -3] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [-2, -2] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [-2, -1] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [-2, 0] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [-2, 1] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [-2, 2] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [-2, 3] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [-2, 4] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [-2, 5] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [-1, -5] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [-1, -4] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_28 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_29 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_30 : subd6_2 [-1, 4] = true := by decide +kernel
theorem subd6_2_31 : subd6_2 [-1, 5] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_cons.2 ⟨subd6_2_28, List.forall_mem_cons.2 ⟨subd6_2_29, List.forall_mem_cons.2 ⟨subd6_2_30, List.forall_mem_cons.2 ⟨subd6_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
