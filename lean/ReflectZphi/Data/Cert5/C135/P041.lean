import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_7_64 : subd8_7 [2, -6] = true := by decide +kernel
theorem subd8_7_65 : subd8_7 [2, -5] = true := by decide +kernel
theorem subd8_7_66 : subd8_7 [2, -4] = true := by decide +kernel
theorem subd8_7_67 : subd8_7 [2, -3] = true := by decide +kernel
theorem subd8_7_68 : subd8_7 [2, -2] = true := by decide +kernel
theorem subd8_7_69 : subd8_7 [2, -1] = true := by decide +kernel
theorem subd8_7_70 : subd8_7 [2, 0] = true := by decide +kernel
theorem subd8_7_71 : subd8_7 [2, 1] = true := by decide +kernel
theorem subd8_7_72 : subd8_7 [2, 2] = true := by decide +kernel
theorem subd8_7_73 : subd8_7 [2, 3] = true := by decide +kernel
theorem subd8_7_74 : subd8_7 [2, 4] = true := by decide +kernel
theorem subd8_7_75 : subd8_7 [3, -6] = true := by decide +kernel
theorem subd8_7_76 : subd8_7 [3, -5] = true := by decide +kernel
theorem subd8_7_77 : subd8_7 [3, -4] = true := by decide +kernel
theorem subd8_7_78 : subd8_7 [3, -3] = true := by decide +kernel
theorem subd8_7_79 : subd8_7 [3, -2] = true := by decide +kernel
theorem subd8_7_80 : subd8_7 [3, -1] = true := by decide +kernel
theorem subd8_7_81 : subd8_7 [3, 0] = true := by decide +kernel
theorem subd8_7_82 : subd8_7 [3, 1] = true := by decide +kernel
theorem subd8_7_83 : subd8_7 [3, 2] = true := by decide +kernel
theorem subd8_7_84 : subd8_7 [3, 3] = true := by decide +kernel
theorem subd8_7_85 : subd8_7 [4, -5] = true := by decide +kernel
theorem subd8_7_86 : subd8_7 [4, -4] = true := by decide +kernel
theorem subd8_7_87 : subd8_7 [4, -3] = true := by decide +kernel
theorem subd8_7_88 : subd8_7 [4, -2] = true := by decide +kernel
theorem subd8_7_89 : subd8_7 [4, -1] = true := by decide +kernel
theorem subd8_7_90 : subd8_7 [4, 0] = true := by decide +kernel
theorem subd8_7_91 : subd8_7 [4, 1] = true := by decide +kernel
theorem subd8_7_92 : subd8_7 [4, 2] = true := by decide +kernel
theorem subd8_7_93 : subd8_7 [5] = true := by decide +kernel
theorem sbd8_7_2 : ∀ q ∈ blkd8_7_2, subd8_7 q = true := by
  unfold blkd8_7_2
  exact List.forall_mem_cons.2 ⟨subd8_7_64, List.forall_mem_cons.2 ⟨subd8_7_65, List.forall_mem_cons.2 ⟨subd8_7_66, List.forall_mem_cons.2 ⟨subd8_7_67, List.forall_mem_cons.2 ⟨subd8_7_68, List.forall_mem_cons.2 ⟨subd8_7_69, List.forall_mem_cons.2 ⟨subd8_7_70, List.forall_mem_cons.2 ⟨subd8_7_71, List.forall_mem_cons.2 ⟨subd8_7_72, List.forall_mem_cons.2 ⟨subd8_7_73, List.forall_mem_cons.2 ⟨subd8_7_74, List.forall_mem_cons.2 ⟨subd8_7_75, List.forall_mem_cons.2 ⟨subd8_7_76, List.forall_mem_cons.2 ⟨subd8_7_77, List.forall_mem_cons.2 ⟨subd8_7_78, List.forall_mem_cons.2 ⟨subd8_7_79, List.forall_mem_cons.2 ⟨subd8_7_80, List.forall_mem_cons.2 ⟨subd8_7_81, List.forall_mem_cons.2 ⟨subd8_7_82, List.forall_mem_cons.2 ⟨subd8_7_83, List.forall_mem_cons.2 ⟨subd8_7_84, List.forall_mem_cons.2 ⟨subd8_7_85, List.forall_mem_cons.2 ⟨subd8_7_86, List.forall_mem_cons.2 ⟨subd8_7_87, List.forall_mem_cons.2 ⟨subd8_7_88, List.forall_mem_cons.2 ⟨subd8_7_89, List.forall_mem_cons.2 ⟨subd8_7_90, List.forall_mem_cons.2 ⟨subd8_7_91, List.forall_mem_cons.2 ⟨subd8_7_92, List.forall_mem_cons.2 ⟨subd8_7_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-5] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-4, -5] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-4, -4] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-4, -3] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-4, -2] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-4, -1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-4, 0] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-4, 1] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-4, 2] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-3, -5] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-3, -4] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-3, -3] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-3, -2] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-3, -1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-3, 0] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-3, 1] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [-3, 2] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [-3, 3] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [-2, -5] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [-2, -4] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [-2, -3] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [-2, -2] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [-2, -1] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [-2, 0] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [-2, 1] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [-2, 2] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [-2, 3] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [-2, 4] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [-1, -5] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [-1, -2] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_32 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [-1, 3] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [-1, 4] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [0, -5] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_40 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_41 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_42 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_43 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_44 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_45 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_46 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_47 : subd9_0 [0, 4] = true := by decide +kernel
theorem subd9_0_48 : subd9_0 [1, -5] = true := by decide +kernel
theorem subd9_0_49 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_50 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_51 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_52 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_53 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_54 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_55 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_56 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_57 : subd9_0 [1, 4] = true := by decide +kernel
theorem subd9_0_58 : subd9_0 [2, -5] = true := by decide +kernel
theorem subd9_0_59 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_60 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_61 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_62 : subd9_0 [2, -1] = true := by decide +kernel
theorem subd9_0_63 : subd9_0 [2, 0] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_cons.2 ⟨subd9_0_40, List.forall_mem_cons.2 ⟨subd9_0_41, List.forall_mem_cons.2 ⟨subd9_0_42, List.forall_mem_cons.2 ⟨subd9_0_43, List.forall_mem_cons.2 ⟨subd9_0_44, List.forall_mem_cons.2 ⟨subd9_0_45, List.forall_mem_cons.2 ⟨subd9_0_46, List.forall_mem_cons.2 ⟨subd9_0_47, List.forall_mem_cons.2 ⟨subd9_0_48, List.forall_mem_cons.2 ⟨subd9_0_49, List.forall_mem_cons.2 ⟨subd9_0_50, List.forall_mem_cons.2 ⟨subd9_0_51, List.forall_mem_cons.2 ⟨subd9_0_52, List.forall_mem_cons.2 ⟨subd9_0_53, List.forall_mem_cons.2 ⟨subd9_0_54, List.forall_mem_cons.2 ⟨subd9_0_55, List.forall_mem_cons.2 ⟨subd9_0_56, List.forall_mem_cons.2 ⟨subd9_0_57, List.forall_mem_cons.2 ⟨subd9_0_58, List.forall_mem_cons.2 ⟨subd9_0_59, List.forall_mem_cons.2 ⟨subd9_0_60, List.forall_mem_cons.2 ⟨subd9_0_61, List.forall_mem_cons.2 ⟨subd9_0_62, List.forall_mem_cons.2 ⟨subd9_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
