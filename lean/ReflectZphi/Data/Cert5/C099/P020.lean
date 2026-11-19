import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_7_32 : subd7_7 [-1, -3] = true := by decide +kernel
theorem subd7_7_33 : subd7_7 [-1, -2] = true := by decide +kernel
theorem subd7_7_34 : subd7_7 [-1, -1] = true := by decide +kernel
theorem subd7_7_35 : subd7_7 [-1, 0] = true := by decide +kernel
theorem subd7_7_36 : subd7_7 [-1, 1] = true := by decide +kernel
theorem subd7_7_37 : subd7_7 [-1, 2] = true := by decide +kernel
theorem subd7_7_38 : subd7_7 [-1, 3] = true := by decide +kernel
theorem subd7_7_39 : subd7_7 [-1, 4] = true := by decide +kernel
theorem subd7_7_40 : subd7_7 [-1, 5] = true := by decide +kernel
theorem subd7_7_41 : subd7_7 [0, -6] = true := by decide +kernel
theorem subd7_7_42 : subd7_7 [0, -5] = true := by decide +kernel
theorem subd7_7_43 : subd7_7 [0, -4] = true := by decide +kernel
theorem subd7_7_44 : subd7_7 [0, -3] = true := by decide +kernel
theorem subd7_7_45 : subd7_7 [0, -2] = true := by decide +kernel
theorem subd7_7_46 : subd7_7 [0, -1] = true := by decide +kernel
theorem subd7_7_47 : subd7_7 [0, 0] = true := by decide +kernel
theorem subd7_7_48 : subd7_7 [0, 1] = true := by decide +kernel
theorem subd7_7_49 : subd7_7 [0, 2] = true := by decide +kernel
theorem subd7_7_50 : subd7_7 [0, 3] = true := by decide +kernel
theorem subd7_7_51 : subd7_7 [0, 4] = true := by decide +kernel
theorem subd7_7_52 : subd7_7 [0, 5] = true := by decide +kernel
theorem subd7_7_53 : subd7_7 [1, -6] = true := by decide +kernel
theorem subd7_7_54 : subd7_7 [1, -5] = true := by decide +kernel
theorem subd7_7_55 : subd7_7 [1, -4] = true := by decide +kernel
theorem subd7_7_56 : subd7_7 [1, -3] = true := by decide +kernel
theorem subd7_7_57 : subd7_7 [1, -2] = true := by decide +kernel
theorem subd7_7_58 : subd7_7 [1, -1] = true := by decide +kernel
theorem subd7_7_59 : subd7_7 [1, 0] = true := by decide +kernel
theorem subd7_7_60 : subd7_7 [1, 1] = true := by decide +kernel
theorem subd7_7_61 : subd7_7 [1, 2] = true := by decide +kernel
theorem subd7_7_62 : subd7_7 [1, 3] = true := by decide +kernel
theorem subd7_7_63 : subd7_7 [1, 4] = true := by decide +kernel
theorem sbd7_7_1 : ∀ q ∈ blkd7_7_1, subd7_7 q = true := by
  unfold blkd7_7_1
  exact List.forall_mem_cons.2 ⟨subd7_7_32, List.forall_mem_cons.2 ⟨subd7_7_33, List.forall_mem_cons.2 ⟨subd7_7_34, List.forall_mem_cons.2 ⟨subd7_7_35, List.forall_mem_cons.2 ⟨subd7_7_36, List.forall_mem_cons.2 ⟨subd7_7_37, List.forall_mem_cons.2 ⟨subd7_7_38, List.forall_mem_cons.2 ⟨subd7_7_39, List.forall_mem_cons.2 ⟨subd7_7_40, List.forall_mem_cons.2 ⟨subd7_7_41, List.forall_mem_cons.2 ⟨subd7_7_42, List.forall_mem_cons.2 ⟨subd7_7_43, List.forall_mem_cons.2 ⟨subd7_7_44, List.forall_mem_cons.2 ⟨subd7_7_45, List.forall_mem_cons.2 ⟨subd7_7_46, List.forall_mem_cons.2 ⟨subd7_7_47, List.forall_mem_cons.2 ⟨subd7_7_48, List.forall_mem_cons.2 ⟨subd7_7_49, List.forall_mem_cons.2 ⟨subd7_7_50, List.forall_mem_cons.2 ⟨subd7_7_51, List.forall_mem_cons.2 ⟨subd7_7_52, List.forall_mem_cons.2 ⟨subd7_7_53, List.forall_mem_cons.2 ⟨subd7_7_54, List.forall_mem_cons.2 ⟨subd7_7_55, List.forall_mem_cons.2 ⟨subd7_7_56, List.forall_mem_cons.2 ⟨subd7_7_57, List.forall_mem_cons.2 ⟨subd7_7_58, List.forall_mem_cons.2 ⟨subd7_7_59, List.forall_mem_cons.2 ⟨subd7_7_60, List.forall_mem_cons.2 ⟨subd7_7_61, List.forall_mem_cons.2 ⟨subd7_7_62, List.forall_mem_cons.2 ⟨subd7_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_7_64 : subd7_7 [1, 5] = true := by decide +kernel
theorem subd7_7_65 : subd7_7 [2, -5] = true := by decide +kernel
theorem subd7_7_66 : subd7_7 [2, -4] = true := by decide +kernel
theorem subd7_7_67 : subd7_7 [2, -3] = true := by decide +kernel
theorem subd7_7_68 : subd7_7 [2, -2] = true := by decide +kernel
theorem subd7_7_69 : subd7_7 [2, -1] = true := by decide +kernel
theorem subd7_7_70 : subd7_7 [2, 0] = true := by decide +kernel
theorem subd7_7_71 : subd7_7 [2, 1] = true := by decide +kernel
theorem subd7_7_72 : subd7_7 [2, 2] = true := by decide +kernel
theorem subd7_7_73 : subd7_7 [2, 3] = true := by decide +kernel
theorem subd7_7_74 : subd7_7 [2, 4] = true := by decide +kernel
theorem subd7_7_75 : subd7_7 [2, 5] = true := by decide +kernel
theorem subd7_7_76 : subd7_7 [3, -4] = true := by decide +kernel
theorem subd7_7_77 : subd7_7 [3, -3] = true := by decide +kernel
theorem subd7_7_78 : subd7_7 [3, -2] = true := by decide +kernel
theorem subd7_7_79 : subd7_7 [3, -1] = true := by decide +kernel
theorem subd7_7_80 : subd7_7 [3, 0] = true := by decide +kernel
theorem subd7_7_81 : subd7_7 [3, 1] = true := by decide +kernel
theorem subd7_7_82 : subd7_7 [3, 2] = true := by decide +kernel
theorem subd7_7_83 : subd7_7 [3, 3] = true := by decide +kernel
theorem subd7_7_84 : subd7_7 [3, 4] = true := by decide +kernel
theorem subd7_7_85 : subd7_7 [4, -3] = true := by decide +kernel
theorem subd7_7_86 : subd7_7 [4, -2] = true := by decide +kernel
theorem subd7_7_87 : subd7_7 [4, -1] = true := by decide +kernel
theorem subd7_7_88 : subd7_7 [4, 0] = true := by decide +kernel
theorem subd7_7_89 : subd7_7 [4, 1] = true := by decide +kernel
theorem subd7_7_90 : subd7_7 [4, 2] = true := by decide +kernel
theorem subd7_7_91 : subd7_7 [4, 3] = true := by decide +kernel
theorem subd7_7_92 : subd7_7 [4, 4] = true := by decide +kernel
theorem subd7_7_93 : subd7_7 [5] = true := by decide +kernel
theorem sbd7_7_2 : ∀ q ∈ blkd7_7_2, subd7_7 q = true := by
  unfold blkd7_7_2
  exact List.forall_mem_cons.2 ⟨subd7_7_64, List.forall_mem_cons.2 ⟨subd7_7_65, List.forall_mem_cons.2 ⟨subd7_7_66, List.forall_mem_cons.2 ⟨subd7_7_67, List.forall_mem_cons.2 ⟨subd7_7_68, List.forall_mem_cons.2 ⟨subd7_7_69, List.forall_mem_cons.2 ⟨subd7_7_70, List.forall_mem_cons.2 ⟨subd7_7_71, List.forall_mem_cons.2 ⟨subd7_7_72, List.forall_mem_cons.2 ⟨subd7_7_73, List.forall_mem_cons.2 ⟨subd7_7_74, List.forall_mem_cons.2 ⟨subd7_7_75, List.forall_mem_cons.2 ⟨subd7_7_76, List.forall_mem_cons.2 ⟨subd7_7_77, List.forall_mem_cons.2 ⟨subd7_7_78, List.forall_mem_cons.2 ⟨subd7_7_79, List.forall_mem_cons.2 ⟨subd7_7_80, List.forall_mem_cons.2 ⟨subd7_7_81, List.forall_mem_cons.2 ⟨subd7_7_82, List.forall_mem_cons.2 ⟨subd7_7_83, List.forall_mem_cons.2 ⟨subd7_7_84, List.forall_mem_cons.2 ⟨subd7_7_85, List.forall_mem_cons.2 ⟨subd7_7_86, List.forall_mem_cons.2 ⟨subd7_7_87, List.forall_mem_cons.2 ⟨subd7_7_88, List.forall_mem_cons.2 ⟨subd7_7_89, List.forall_mem_cons.2 ⟨subd7_7_90, List.forall_mem_cons.2 ⟨subd7_7_91, List.forall_mem_cons.2 ⟨subd7_7_92, List.forall_mem_cons.2 ⟨subd7_7_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [1] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [0, 0, -9] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [0, 0, -8] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [0, 0, 7] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [0, 0, 8] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [0, 1] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-2] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-1, -2] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-1, -1] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-1, 0] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-1, 1] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-1, 2] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [1, -1] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [1, 0] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [1, 1] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
