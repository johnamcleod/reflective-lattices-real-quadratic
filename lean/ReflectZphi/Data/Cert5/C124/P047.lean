import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_10_32 : subd8_10 [0, 1] = true := by decide +kernel
theorem subd8_10_33 : subd8_10 [0, 2] = true := by decide +kernel
theorem subd8_10_34 : subd8_10 [0, 3] = true := by decide +kernel
theorem subd8_10_35 : subd8_10 [1, -4] = true := by decide +kernel
theorem subd8_10_36 : subd8_10 [1, -3] = true := by decide +kernel
theorem subd8_10_37 : subd8_10 [1, -2] = true := by decide +kernel
theorem subd8_10_38 : subd8_10 [1, -1] = true := by decide +kernel
theorem subd8_10_39 : subd8_10 [1, 0] = true := by decide +kernel
theorem subd8_10_40 : subd8_10 [1, 1] = true := by decide +kernel
theorem subd8_10_41 : subd8_10 [1, 2] = true := by decide +kernel
theorem subd8_10_42 : subd8_10 [2, -4] = true := by decide +kernel
theorem subd8_10_43 : subd8_10 [2, -3] = true := by decide +kernel
theorem subd8_10_44 : subd8_10 [2, -2] = true := by decide +kernel
theorem subd8_10_45 : subd8_10 [2, -1] = true := by decide +kernel
theorem subd8_10_46 : subd8_10 [2, 0] = true := by decide +kernel
theorem subd8_10_47 : subd8_10 [2, 1] = true := by decide +kernel
theorem subd8_10_48 : subd8_10 [3] = true := by decide +kernel
theorem sbd8_10_1 : ∀ q ∈ blkd8_10_1, subd8_10 q = true := by
  unfold blkd8_10_1
  exact List.forall_mem_cons.2 ⟨subd8_10_32, List.forall_mem_cons.2 ⟨subd8_10_33, List.forall_mem_cons.2 ⟨subd8_10_34, List.forall_mem_cons.2 ⟨subd8_10_35, List.forall_mem_cons.2 ⟨subd8_10_36, List.forall_mem_cons.2 ⟨subd8_10_37, List.forall_mem_cons.2 ⟨subd8_10_38, List.forall_mem_cons.2 ⟨subd8_10_39, List.forall_mem_cons.2 ⟨subd8_10_40, List.forall_mem_cons.2 ⟨subd8_10_41, List.forall_mem_cons.2 ⟨subd8_10_42, List.forall_mem_cons.2 ⟨subd8_10_43, List.forall_mem_cons.2 ⟨subd8_10_44, List.forall_mem_cons.2 ⟨subd8_10_45, List.forall_mem_cons.2 ⟨subd8_10_46, List.forall_mem_cons.2 ⟨subd8_10_47, List.forall_mem_cons.2 ⟨subd8_10_48, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_11 : ldCheck G d8_11.U d8_11.ms ldd8_11 = true := by decide +kernel
theorem pre_okd8_11 : subPre G cell8 d8_11 = true := by decide +kernel
theorem subd8_11_0 : subd8_11 [-5] = true := by decide +kernel
theorem subd8_11_1 : subd8_11 [-4, -5] = true := by decide +kernel
theorem subd8_11_2 : subd8_11 [-4, -4] = true := by decide +kernel
theorem subd8_11_3 : subd8_11 [-4, -3] = true := by decide +kernel
theorem subd8_11_4 : subd8_11 [-4, -2] = true := by decide +kernel
theorem subd8_11_5 : subd8_11 [-4, -1] = true := by decide +kernel
theorem subd8_11_6 : subd8_11 [-4, 0] = true := by decide +kernel
theorem subd8_11_7 : subd8_11 [-4, 1] = true := by decide +kernel
theorem subd8_11_8 : subd8_11 [-4, 2] = true := by decide +kernel
theorem subd8_11_9 : subd8_11 [-4, 3] = true := by decide +kernel
theorem subd8_11_10 : subd8_11 [-3, -6] = true := by decide +kernel
theorem subd8_11_11 : subd8_11 [-3, -5] = true := by decide +kernel
theorem subd8_11_12 : subd8_11 [-3, -4] = true := by decide +kernel
theorem subd8_11_13 : subd8_11 [-3, -3] = true := by decide +kernel
theorem subd8_11_14 : subd8_11 [-3, -2] = true := by decide +kernel
theorem subd8_11_15 : subd8_11 [-3, -1] = true := by decide +kernel
theorem subd8_11_16 : subd8_11 [-3, 0] = true := by decide +kernel
theorem subd8_11_17 : subd8_11 [-3, 1] = true := by decide +kernel
theorem subd8_11_18 : subd8_11 [-3, 2] = true := by decide +kernel
theorem subd8_11_19 : subd8_11 [-3, 3] = true := by decide +kernel
theorem subd8_11_20 : subd8_11 [-3, 4] = true := by decide +kernel
theorem subd8_11_21 : subd8_11 [-2, -6] = true := by decide +kernel
theorem subd8_11_22 : subd8_11 [-2, -5] = true := by decide +kernel
theorem subd8_11_23 : subd8_11 [-2, -4] = true := by decide +kernel
theorem subd8_11_24 : subd8_11 [-2, -3] = true := by decide +kernel
theorem subd8_11_25 : subd8_11 [-2, -2] = true := by decide +kernel
theorem subd8_11_26 : subd8_11 [-2, -1] = true := by decide +kernel
theorem subd8_11_27 : subd8_11 [-2, 0] = true := by decide +kernel
theorem subd8_11_28 : subd8_11 [-2, 1] = true := by decide +kernel
theorem subd8_11_29 : subd8_11 [-2, 2] = true := by decide +kernel
theorem subd8_11_30 : subd8_11 [-2, 3] = true := by decide +kernel
theorem subd8_11_31 : subd8_11 [-2, 4] = true := by decide +kernel
theorem sbd8_11_0 : ∀ q ∈ blkd8_11_0, subd8_11 q = true := by
  unfold blkd8_11_0
  exact List.forall_mem_cons.2 ⟨subd8_11_0, List.forall_mem_cons.2 ⟨subd8_11_1, List.forall_mem_cons.2 ⟨subd8_11_2, List.forall_mem_cons.2 ⟨subd8_11_3, List.forall_mem_cons.2 ⟨subd8_11_4, List.forall_mem_cons.2 ⟨subd8_11_5, List.forall_mem_cons.2 ⟨subd8_11_6, List.forall_mem_cons.2 ⟨subd8_11_7, List.forall_mem_cons.2 ⟨subd8_11_8, List.forall_mem_cons.2 ⟨subd8_11_9, List.forall_mem_cons.2 ⟨subd8_11_10, List.forall_mem_cons.2 ⟨subd8_11_11, List.forall_mem_cons.2 ⟨subd8_11_12, List.forall_mem_cons.2 ⟨subd8_11_13, List.forall_mem_cons.2 ⟨subd8_11_14, List.forall_mem_cons.2 ⟨subd8_11_15, List.forall_mem_cons.2 ⟨subd8_11_16, List.forall_mem_cons.2 ⟨subd8_11_17, List.forall_mem_cons.2 ⟨subd8_11_18, List.forall_mem_cons.2 ⟨subd8_11_19, List.forall_mem_cons.2 ⟨subd8_11_20, List.forall_mem_cons.2 ⟨subd8_11_21, List.forall_mem_cons.2 ⟨subd8_11_22, List.forall_mem_cons.2 ⟨subd8_11_23, List.forall_mem_cons.2 ⟨subd8_11_24, List.forall_mem_cons.2 ⟨subd8_11_25, List.forall_mem_cons.2 ⟨subd8_11_26, List.forall_mem_cons.2 ⟨subd8_11_27, List.forall_mem_cons.2 ⟨subd8_11_28, List.forall_mem_cons.2 ⟨subd8_11_29, List.forall_mem_cons.2 ⟨subd8_11_30, List.forall_mem_cons.2 ⟨subd8_11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_11_32 : subd8_11 [-2, 5] = true := by decide +kernel
theorem subd8_11_33 : subd8_11 [-1, -6] = true := by decide +kernel
theorem subd8_11_34 : subd8_11 [-1, -5] = true := by decide +kernel
theorem subd8_11_35 : subd8_11 [-1, -4] = true := by decide +kernel
theorem subd8_11_36 : subd8_11 [-1, -3] = true := by decide +kernel
theorem subd8_11_37 : subd8_11 [-1, -2] = true := by decide +kernel
theorem subd8_11_38 : subd8_11 [-1, -1] = true := by decide +kernel
theorem subd8_11_39 : subd8_11 [-1, 0] = true := by decide +kernel
theorem subd8_11_40 : subd8_11 [-1, 1] = true := by decide +kernel
theorem subd8_11_41 : subd8_11 [-1, 2] = true := by decide +kernel
theorem subd8_11_42 : subd8_11 [-1, 3] = true := by decide +kernel
theorem subd8_11_43 : subd8_11 [-1, 4] = true := by decide +kernel
theorem subd8_11_44 : subd8_11 [-1, 5] = true := by decide +kernel
theorem subd8_11_45 : subd8_11 [0, -6] = true := by decide +kernel
theorem subd8_11_46 : subd8_11 [0, -5] = true := by decide +kernel
theorem subd8_11_47 : subd8_11 [0, -4] = true := by decide +kernel
theorem subd8_11_48 : subd8_11 [0, -3] = true := by decide +kernel
theorem subd8_11_49 : subd8_11 [0, -2] = true := by decide +kernel
theorem subd8_11_50 : subd8_11 [0, -1] = true := by decide +kernel
theorem subd8_11_51 : subd8_11 [0, 0] = true := by decide +kernel
theorem subd8_11_52 : subd8_11 [0, 1] = true := by decide +kernel
theorem subd8_11_53 : subd8_11 [0, 2] = true := by decide +kernel
theorem subd8_11_54 : subd8_11 [0, 3] = true := by decide +kernel
theorem subd8_11_55 : subd8_11 [0, 4] = true := by decide +kernel
theorem subd8_11_56 : subd8_11 [0, 5] = true := by decide +kernel
theorem subd8_11_57 : subd8_11 [1, -6] = true := by decide +kernel
theorem subd8_11_58 : subd8_11 [1, -5] = true := by decide +kernel
theorem subd8_11_59 : subd8_11 [1, -4] = true := by decide +kernel
theorem subd8_11_60 : subd8_11 [1, -3] = true := by decide +kernel
theorem subd8_11_61 : subd8_11 [1, -2] = true := by decide +kernel
theorem subd8_11_62 : subd8_11 [1, -1] = true := by decide +kernel
theorem subd8_11_63 : subd8_11 [1, 0] = true := by decide +kernel
theorem sbd8_11_1 : ∀ q ∈ blkd8_11_1, subd8_11 q = true := by
  unfold blkd8_11_1
  exact List.forall_mem_cons.2 ⟨subd8_11_32, List.forall_mem_cons.2 ⟨subd8_11_33, List.forall_mem_cons.2 ⟨subd8_11_34, List.forall_mem_cons.2 ⟨subd8_11_35, List.forall_mem_cons.2 ⟨subd8_11_36, List.forall_mem_cons.2 ⟨subd8_11_37, List.forall_mem_cons.2 ⟨subd8_11_38, List.forall_mem_cons.2 ⟨subd8_11_39, List.forall_mem_cons.2 ⟨subd8_11_40, List.forall_mem_cons.2 ⟨subd8_11_41, List.forall_mem_cons.2 ⟨subd8_11_42, List.forall_mem_cons.2 ⟨subd8_11_43, List.forall_mem_cons.2 ⟨subd8_11_44, List.forall_mem_cons.2 ⟨subd8_11_45, List.forall_mem_cons.2 ⟨subd8_11_46, List.forall_mem_cons.2 ⟨subd8_11_47, List.forall_mem_cons.2 ⟨subd8_11_48, List.forall_mem_cons.2 ⟨subd8_11_49, List.forall_mem_cons.2 ⟨subd8_11_50, List.forall_mem_cons.2 ⟨subd8_11_51, List.forall_mem_cons.2 ⟨subd8_11_52, List.forall_mem_cons.2 ⟨subd8_11_53, List.forall_mem_cons.2 ⟨subd8_11_54, List.forall_mem_cons.2 ⟨subd8_11_55, List.forall_mem_cons.2 ⟨subd8_11_56, List.forall_mem_cons.2 ⟨subd8_11_57, List.forall_mem_cons.2 ⟨subd8_11_58, List.forall_mem_cons.2 ⟨subd8_11_59, List.forall_mem_cons.2 ⟨subd8_11_60, List.forall_mem_cons.2 ⟨subd8_11_61, List.forall_mem_cons.2 ⟨subd8_11_62, List.forall_mem_cons.2 ⟨subd8_11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_11_64 : subd8_11 [1, 1] = true := by decide +kernel
theorem subd8_11_65 : subd8_11 [1, 2] = true := by decide +kernel
theorem subd8_11_66 : subd8_11 [1, 3] = true := by decide +kernel
theorem subd8_11_67 : subd8_11 [1, 4] = true := by decide +kernel
theorem subd8_11_68 : subd8_11 [1, 5] = true := by decide +kernel
theorem subd8_11_69 : subd8_11 [2, -6] = true := by decide +kernel
theorem subd8_11_70 : subd8_11 [2, -5] = true := by decide +kernel
theorem subd8_11_71 : subd8_11 [2, -4] = true := by decide +kernel
theorem subd8_11_72 : subd8_11 [2, -3] = true := by decide +kernel
theorem subd8_11_73 : subd8_11 [2, -2] = true := by decide +kernel
theorem subd8_11_74 : subd8_11 [2, -1] = true := by decide +kernel
theorem subd8_11_75 : subd8_11 [2, 0] = true := by decide +kernel
theorem subd8_11_76 : subd8_11 [2, 1] = true := by decide +kernel
theorem subd8_11_77 : subd8_11 [2, 2] = true := by decide +kernel
theorem subd8_11_78 : subd8_11 [2, 3] = true := by decide +kernel
theorem subd8_11_79 : subd8_11 [2, 4] = true := by decide +kernel
theorem subd8_11_80 : subd8_11 [2, 5] = true := by decide +kernel
theorem subd8_11_81 : subd8_11 [3, -5] = true := by decide +kernel
theorem subd8_11_82 : subd8_11 [3, -4] = true := by decide +kernel
theorem subd8_11_83 : subd8_11 [3, -3] = true := by decide +kernel
theorem subd8_11_84 : subd8_11 [3, -2] = true := by decide +kernel
theorem subd8_11_85 : subd8_11 [3, -1] = true := by decide +kernel
theorem subd8_11_86 : subd8_11 [3, 0] = true := by decide +kernel
theorem subd8_11_87 : subd8_11 [3, 1] = true := by decide +kernel
theorem subd8_11_88 : subd8_11 [3, 2] = true := by decide +kernel
theorem subd8_11_89 : subd8_11 [3, 3] = true := by decide +kernel
theorem subd8_11_90 : subd8_11 [3, 4] = true := by decide +kernel
theorem subd8_11_91 : subd8_11 [3, 5] = true := by decide +kernel
theorem subd8_11_92 : subd8_11 [4, -4] = true := by decide +kernel
theorem subd8_11_93 : subd8_11 [4, -3] = true := by decide +kernel
theorem subd8_11_94 : subd8_11 [4, -2] = true := by decide +kernel
theorem subd8_11_95 : subd8_11 [4, -1] = true := by decide +kernel
theorem sbd8_11_2 : ∀ q ∈ blkd8_11_2, subd8_11 q = true := by
  unfold blkd8_11_2
  exact List.forall_mem_cons.2 ⟨subd8_11_64, List.forall_mem_cons.2 ⟨subd8_11_65, List.forall_mem_cons.2 ⟨subd8_11_66, List.forall_mem_cons.2 ⟨subd8_11_67, List.forall_mem_cons.2 ⟨subd8_11_68, List.forall_mem_cons.2 ⟨subd8_11_69, List.forall_mem_cons.2 ⟨subd8_11_70, List.forall_mem_cons.2 ⟨subd8_11_71, List.forall_mem_cons.2 ⟨subd8_11_72, List.forall_mem_cons.2 ⟨subd8_11_73, List.forall_mem_cons.2 ⟨subd8_11_74, List.forall_mem_cons.2 ⟨subd8_11_75, List.forall_mem_cons.2 ⟨subd8_11_76, List.forall_mem_cons.2 ⟨subd8_11_77, List.forall_mem_cons.2 ⟨subd8_11_78, List.forall_mem_cons.2 ⟨subd8_11_79, List.forall_mem_cons.2 ⟨subd8_11_80, List.forall_mem_cons.2 ⟨subd8_11_81, List.forall_mem_cons.2 ⟨subd8_11_82, List.forall_mem_cons.2 ⟨subd8_11_83, List.forall_mem_cons.2 ⟨subd8_11_84, List.forall_mem_cons.2 ⟨subd8_11_85, List.forall_mem_cons.2 ⟨subd8_11_86, List.forall_mem_cons.2 ⟨subd8_11_87, List.forall_mem_cons.2 ⟨subd8_11_88, List.forall_mem_cons.2 ⟨subd8_11_89, List.forall_mem_cons.2 ⟨subd8_11_90, List.forall_mem_cons.2 ⟨subd8_11_91, List.forall_mem_cons.2 ⟨subd8_11_92, List.forall_mem_cons.2 ⟨subd8_11_93, List.forall_mem_cons.2 ⟨subd8_11_94, List.forall_mem_cons.2 ⟨subd8_11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_11_96 : subd8_11 [4, 0] = true := by decide +kernel
theorem subd8_11_97 : subd8_11 [4, 1] = true := by decide +kernel
theorem subd8_11_98 : subd8_11 [4, 2] = true := by decide +kernel
theorem subd8_11_99 : subd8_11 [4, 3] = true := by decide +kernel
theorem subd8_11_100 : subd8_11 [4, 4] = true := by decide +kernel
theorem subd8_11_101 : subd8_11 [5] = true := by decide +kernel
theorem sbd8_11_3 : ∀ q ∈ blkd8_11_3, subd8_11 q = true := by
  unfold blkd8_11_3
  exact List.forall_mem_cons.2 ⟨subd8_11_96, List.forall_mem_cons.2 ⟨subd8_11_97, List.forall_mem_cons.2 ⟨subd8_11_98, List.forall_mem_cons.2 ⟨subd8_11_99, List.forall_mem_cons.2 ⟨subd8_11_100, List.forall_mem_cons.2 ⟨subd8_11_101, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
