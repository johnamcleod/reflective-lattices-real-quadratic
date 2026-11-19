import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd20_2_64 : subd20_2 [1, 3] = true := by decide +kernel
theorem subd20_2_65 : subd20_2 [1, 4] = true := by decide +kernel
theorem subd20_2_66 : subd20_2 [1, 5] = true := by decide +kernel
theorem subd20_2_67 : subd20_2 [2, -6] = true := by decide +kernel
theorem subd20_2_68 : subd20_2 [2, -5] = true := by decide +kernel
theorem subd20_2_69 : subd20_2 [2, -4] = true := by decide +kernel
theorem subd20_2_70 : subd20_2 [2, -3] = true := by decide +kernel
theorem subd20_2_71 : subd20_2 [2, -2] = true := by decide +kernel
theorem subd20_2_72 : subd20_2 [2, -1] = true := by decide +kernel
theorem subd20_2_73 : subd20_2 [2, 0] = true := by decide +kernel
theorem subd20_2_74 : subd20_2 [2, 1] = true := by decide +kernel
theorem subd20_2_75 : subd20_2 [2, 2] = true := by decide +kernel
theorem subd20_2_76 : subd20_2 [2, 3] = true := by decide +kernel
theorem subd20_2_77 : subd20_2 [2, 4] = true := by decide +kernel
theorem subd20_2_78 : subd20_2 [3, -6] = true := by decide +kernel
theorem subd20_2_79 : subd20_2 [3, -5] = true := by decide +kernel
theorem subd20_2_80 : subd20_2 [3, -4] = true := by decide +kernel
theorem subd20_2_81 : subd20_2 [3, -3] = true := by decide +kernel
theorem subd20_2_82 : subd20_2 [3, -2] = true := by decide +kernel
theorem subd20_2_83 : subd20_2 [3, -1] = true := by decide +kernel
theorem subd20_2_84 : subd20_2 [3, 0] = true := by decide +kernel
theorem subd20_2_85 : subd20_2 [3, 1] = true := by decide +kernel
theorem subd20_2_86 : subd20_2 [3, 2] = true := by decide +kernel
theorem subd20_2_87 : subd20_2 [3, 3] = true := by decide +kernel
theorem subd20_2_88 : subd20_2 [4, -5] = true := by decide +kernel
theorem subd20_2_89 : subd20_2 [4, -4] = true := by decide +kernel
theorem subd20_2_90 : subd20_2 [4, -3] = true := by decide +kernel
theorem subd20_2_91 : subd20_2 [4, -2] = true := by decide +kernel
theorem subd20_2_92 : subd20_2 [4, -1] = true := by decide +kernel
theorem subd20_2_93 : subd20_2 [4, 0] = true := by decide +kernel
theorem subd20_2_94 : subd20_2 [4, 1] = true := by decide +kernel
theorem subd20_2_95 : subd20_2 [4, 2] = true := by decide +kernel
theorem sbd20_2_2 : ∀ q ∈ blkd20_2_2, subd20_2 q = true := by
  unfold blkd20_2_2
  exact List.forall_mem_cons.2 ⟨subd20_2_64, List.forall_mem_cons.2 ⟨subd20_2_65, List.forall_mem_cons.2 ⟨subd20_2_66, List.forall_mem_cons.2 ⟨subd20_2_67, List.forall_mem_cons.2 ⟨subd20_2_68, List.forall_mem_cons.2 ⟨subd20_2_69, List.forall_mem_cons.2 ⟨subd20_2_70, List.forall_mem_cons.2 ⟨subd20_2_71, List.forall_mem_cons.2 ⟨subd20_2_72, List.forall_mem_cons.2 ⟨subd20_2_73, List.forall_mem_cons.2 ⟨subd20_2_74, List.forall_mem_cons.2 ⟨subd20_2_75, List.forall_mem_cons.2 ⟨subd20_2_76, List.forall_mem_cons.2 ⟨subd20_2_77, List.forall_mem_cons.2 ⟨subd20_2_78, List.forall_mem_cons.2 ⟨subd20_2_79, List.forall_mem_cons.2 ⟨subd20_2_80, List.forall_mem_cons.2 ⟨subd20_2_81, List.forall_mem_cons.2 ⟨subd20_2_82, List.forall_mem_cons.2 ⟨subd20_2_83, List.forall_mem_cons.2 ⟨subd20_2_84, List.forall_mem_cons.2 ⟨subd20_2_85, List.forall_mem_cons.2 ⟨subd20_2_86, List.forall_mem_cons.2 ⟨subd20_2_87, List.forall_mem_cons.2 ⟨subd20_2_88, List.forall_mem_cons.2 ⟨subd20_2_89, List.forall_mem_cons.2 ⟨subd20_2_90, List.forall_mem_cons.2 ⟨subd20_2_91, List.forall_mem_cons.2 ⟨subd20_2_92, List.forall_mem_cons.2 ⟨subd20_2_93, List.forall_mem_cons.2 ⟨subd20_2_94, List.forall_mem_cons.2 ⟨subd20_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd20_3 : ldCheck G d20_3.U d20_3.ms ldd20_3 = true := by decide +kernel
theorem pre_okd20_3 : subPre G cell20 d20_3 = true := by decide +kernel
theorem subd20_3_0 : subd20_3 [-5] = true := by decide +kernel
theorem subd20_3_1 : subd20_3 [-4, -5] = true := by decide +kernel
theorem subd20_3_2 : subd20_3 [-4, -4] = true := by decide +kernel
theorem subd20_3_3 : subd20_3 [-4, -3] = true := by decide +kernel
theorem subd20_3_4 : subd20_3 [-4, -2] = true := by decide +kernel
theorem subd20_3_5 : subd20_3 [-4, -1] = true := by decide +kernel
theorem subd20_3_6 : subd20_3 [-4, 0] = true := by decide +kernel
theorem subd20_3_7 : subd20_3 [-4, 1] = true := by decide +kernel
theorem subd20_3_8 : subd20_3 [-4, 2] = true := by decide +kernel
theorem subd20_3_9 : subd20_3 [-3, -6] = true := by decide +kernel
theorem subd20_3_10 : subd20_3 [-3, -5] = true := by decide +kernel
theorem subd20_3_11 : subd20_3 [-3, -4] = true := by decide +kernel
theorem subd20_3_12 : subd20_3 [-3, -3] = true := by decide +kernel
theorem subd20_3_13 : subd20_3 [-3, -2] = true := by decide +kernel
theorem subd20_3_14 : subd20_3 [-3, -1] = true := by decide +kernel
theorem subd20_3_15 : subd20_3 [-3, 0] = true := by decide +kernel
theorem subd20_3_16 : subd20_3 [-3, 1] = true := by decide +kernel
theorem subd20_3_17 : subd20_3 [-3, 2] = true := by decide +kernel
theorem subd20_3_18 : subd20_3 [-3, 3] = true := by decide +kernel
theorem subd20_3_19 : subd20_3 [-2, -6] = true := by decide +kernel
theorem subd20_3_20 : subd20_3 [-2, -5] = true := by decide +kernel
theorem subd20_3_21 : subd20_3 [-2, -4] = true := by decide +kernel
theorem subd20_3_22 : subd20_3 [-2, -3] = true := by decide +kernel
theorem subd20_3_23 : subd20_3 [-2, -2] = true := by decide +kernel
theorem subd20_3_24 : subd20_3 [-2, -1] = true := by decide +kernel
theorem subd20_3_25 : subd20_3 [-2, 0] = true := by decide +kernel
theorem subd20_3_26 : subd20_3 [-2, 1] = true := by decide +kernel
theorem subd20_3_27 : subd20_3 [-2, 2] = true := by decide +kernel
theorem subd20_3_28 : subd20_3 [-2, 3] = true := by decide +kernel
theorem subd20_3_29 : subd20_3 [-2, 4] = true := by decide +kernel
theorem subd20_3_30 : subd20_3 [-1, -6] = true := by decide +kernel
theorem subd20_3_31 : subd20_3 [-1, -5] = true := by decide +kernel
theorem sbd20_3_0 : ∀ q ∈ blkd20_3_0, subd20_3 q = true := by
  unfold blkd20_3_0
  exact List.forall_mem_cons.2 ⟨subd20_3_0, List.forall_mem_cons.2 ⟨subd20_3_1, List.forall_mem_cons.2 ⟨subd20_3_2, List.forall_mem_cons.2 ⟨subd20_3_3, List.forall_mem_cons.2 ⟨subd20_3_4, List.forall_mem_cons.2 ⟨subd20_3_5, List.forall_mem_cons.2 ⟨subd20_3_6, List.forall_mem_cons.2 ⟨subd20_3_7, List.forall_mem_cons.2 ⟨subd20_3_8, List.forall_mem_cons.2 ⟨subd20_3_9, List.forall_mem_cons.2 ⟨subd20_3_10, List.forall_mem_cons.2 ⟨subd20_3_11, List.forall_mem_cons.2 ⟨subd20_3_12, List.forall_mem_cons.2 ⟨subd20_3_13, List.forall_mem_cons.2 ⟨subd20_3_14, List.forall_mem_cons.2 ⟨subd20_3_15, List.forall_mem_cons.2 ⟨subd20_3_16, List.forall_mem_cons.2 ⟨subd20_3_17, List.forall_mem_cons.2 ⟨subd20_3_18, List.forall_mem_cons.2 ⟨subd20_3_19, List.forall_mem_cons.2 ⟨subd20_3_20, List.forall_mem_cons.2 ⟨subd20_3_21, List.forall_mem_cons.2 ⟨subd20_3_22, List.forall_mem_cons.2 ⟨subd20_3_23, List.forall_mem_cons.2 ⟨subd20_3_24, List.forall_mem_cons.2 ⟨subd20_3_25, List.forall_mem_cons.2 ⟨subd20_3_26, List.forall_mem_cons.2 ⟨subd20_3_27, List.forall_mem_cons.2 ⟨subd20_3_28, List.forall_mem_cons.2 ⟨subd20_3_29, List.forall_mem_cons.2 ⟨subd20_3_30, List.forall_mem_cons.2 ⟨subd20_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_3_32 : subd20_3 [-1, -4] = true := by decide +kernel
theorem subd20_3_33 : subd20_3 [-1, -3] = true := by decide +kernel
theorem subd20_3_34 : subd20_3 [-1, -2] = true := by decide +kernel
theorem subd20_3_35 : subd20_3 [-1, -1] = true := by decide +kernel
theorem subd20_3_36 : subd20_3 [-1, 0] = true := by decide +kernel
theorem subd20_3_37 : subd20_3 [-1, 1] = true := by decide +kernel
theorem subd20_3_38 : subd20_3 [-1, 2] = true := by decide +kernel
theorem subd20_3_39 : subd20_3 [-1, 3] = true := by decide +kernel
theorem subd20_3_40 : subd20_3 [-1, 4] = true := by decide +kernel
theorem subd20_3_41 : subd20_3 [-1, 5] = true := by decide +kernel
theorem subd20_3_42 : subd20_3 [0, -6] = true := by decide +kernel
theorem subd20_3_43 : subd20_3 [0, -5] = true := by decide +kernel
theorem subd20_3_44 : subd20_3 [0, -4] = true := by decide +kernel
theorem subd20_3_45 : subd20_3 [0, -3] = true := by decide +kernel
theorem subd20_3_46 : subd20_3 [0, -2] = true := by decide +kernel
theorem subd20_3_47 : subd20_3 [0, -1] = true := by decide +kernel
theorem subd20_3_48 : subd20_3 [0, 0] = true := by decide +kernel
theorem subd20_3_49 : subd20_3 [0, 1] = true := by decide +kernel
theorem subd20_3_50 : subd20_3 [0, 2] = true := by decide +kernel
theorem subd20_3_51 : subd20_3 [0, 3] = true := by decide +kernel
theorem subd20_3_52 : subd20_3 [0, 4] = true := by decide +kernel
theorem subd20_3_53 : subd20_3 [0, 5] = true := by decide +kernel
theorem subd20_3_54 : subd20_3 [1, -6] = true := by decide +kernel
theorem subd20_3_55 : subd20_3 [1, -5] = true := by decide +kernel
theorem subd20_3_56 : subd20_3 [1, -4] = true := by decide +kernel
theorem subd20_3_57 : subd20_3 [1, -3] = true := by decide +kernel
theorem subd20_3_58 : subd20_3 [1, -2] = true := by decide +kernel
theorem subd20_3_59 : subd20_3 [1, -1] = true := by decide +kernel
theorem subd20_3_60 : subd20_3 [1, 0] = true := by decide +kernel
theorem subd20_3_61 : subd20_3 [1, 1] = true := by decide +kernel
theorem subd20_3_62 : subd20_3 [1, 2] = true := by decide +kernel
theorem subd20_3_63 : subd20_3 [1, 3] = true := by decide +kernel
theorem sbd20_3_1 : ∀ q ∈ blkd20_3_1, subd20_3 q = true := by
  unfold blkd20_3_1
  exact List.forall_mem_cons.2 ⟨subd20_3_32, List.forall_mem_cons.2 ⟨subd20_3_33, List.forall_mem_cons.2 ⟨subd20_3_34, List.forall_mem_cons.2 ⟨subd20_3_35, List.forall_mem_cons.2 ⟨subd20_3_36, List.forall_mem_cons.2 ⟨subd20_3_37, List.forall_mem_cons.2 ⟨subd20_3_38, List.forall_mem_cons.2 ⟨subd20_3_39, List.forall_mem_cons.2 ⟨subd20_3_40, List.forall_mem_cons.2 ⟨subd20_3_41, List.forall_mem_cons.2 ⟨subd20_3_42, List.forall_mem_cons.2 ⟨subd20_3_43, List.forall_mem_cons.2 ⟨subd20_3_44, List.forall_mem_cons.2 ⟨subd20_3_45, List.forall_mem_cons.2 ⟨subd20_3_46, List.forall_mem_cons.2 ⟨subd20_3_47, List.forall_mem_cons.2 ⟨subd20_3_48, List.forall_mem_cons.2 ⟨subd20_3_49, List.forall_mem_cons.2 ⟨subd20_3_50, List.forall_mem_cons.2 ⟨subd20_3_51, List.forall_mem_cons.2 ⟨subd20_3_52, List.forall_mem_cons.2 ⟨subd20_3_53, List.forall_mem_cons.2 ⟨subd20_3_54, List.forall_mem_cons.2 ⟨subd20_3_55, List.forall_mem_cons.2 ⟨subd20_3_56, List.forall_mem_cons.2 ⟨subd20_3_57, List.forall_mem_cons.2 ⟨subd20_3_58, List.forall_mem_cons.2 ⟨subd20_3_59, List.forall_mem_cons.2 ⟨subd20_3_60, List.forall_mem_cons.2 ⟨subd20_3_61, List.forall_mem_cons.2 ⟨subd20_3_62, List.forall_mem_cons.2 ⟨subd20_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_3_64 : subd20_3 [1, 4] = true := by decide +kernel
theorem subd20_3_65 : subd20_3 [1, 5] = true := by decide +kernel
theorem subd20_3_66 : subd20_3 [2, -5] = true := by decide +kernel
theorem subd20_3_67 : subd20_3 [2, -4] = true := by decide +kernel
theorem subd20_3_68 : subd20_3 [2, -3] = true := by decide +kernel
theorem subd20_3_69 : subd20_3 [2, -2] = true := by decide +kernel
theorem subd20_3_70 : subd20_3 [2, -1] = true := by decide +kernel
theorem subd20_3_71 : subd20_3 [2, 0] = true := by decide +kernel
theorem subd20_3_72 : subd20_3 [2, 1] = true := by decide +kernel
theorem subd20_3_73 : subd20_3 [2, 2] = true := by decide +kernel
theorem subd20_3_74 : subd20_3 [2, 3] = true := by decide +kernel
theorem subd20_3_75 : subd20_3 [2, 4] = true := by decide +kernel
theorem subd20_3_76 : subd20_3 [2, 5] = true := by decide +kernel
theorem subd20_3_77 : subd20_3 [3, -4] = true := by decide +kernel
theorem subd20_3_78 : subd20_3 [3, -3] = true := by decide +kernel
theorem subd20_3_79 : subd20_3 [3, -2] = true := by decide +kernel
theorem subd20_3_80 : subd20_3 [3, -1] = true := by decide +kernel
theorem subd20_3_81 : subd20_3 [3, 0] = true := by decide +kernel
theorem subd20_3_82 : subd20_3 [3, 1] = true := by decide +kernel
theorem subd20_3_83 : subd20_3 [3, 2] = true := by decide +kernel
theorem subd20_3_84 : subd20_3 [3, 3] = true := by decide +kernel
theorem subd20_3_85 : subd20_3 [3, 4] = true := by decide +kernel
theorem subd20_3_86 : subd20_3 [3, 5] = true := by decide +kernel
theorem subd20_3_87 : subd20_3 [4, -3] = true := by decide +kernel
theorem subd20_3_88 : subd20_3 [4, -2] = true := by decide +kernel
theorem subd20_3_89 : subd20_3 [4, -1] = true := by decide +kernel
theorem subd20_3_90 : subd20_3 [4, 0] = true := by decide +kernel
theorem subd20_3_91 : subd20_3 [4, 1] = true := by decide +kernel
theorem subd20_3_92 : subd20_3 [4, 2] = true := by decide +kernel
theorem subd20_3_93 : subd20_3 [4, 3] = true := by decide +kernel
theorem subd20_3_94 : subd20_3 [4, 4] = true := by decide +kernel
theorem subd20_3_95 : subd20_3 [5] = true := by decide +kernel
theorem sbd20_3_2 : ∀ q ∈ blkd20_3_2, subd20_3 q = true := by
  unfold blkd20_3_2
  exact List.forall_mem_cons.2 ⟨subd20_3_64, List.forall_mem_cons.2 ⟨subd20_3_65, List.forall_mem_cons.2 ⟨subd20_3_66, List.forall_mem_cons.2 ⟨subd20_3_67, List.forall_mem_cons.2 ⟨subd20_3_68, List.forall_mem_cons.2 ⟨subd20_3_69, List.forall_mem_cons.2 ⟨subd20_3_70, List.forall_mem_cons.2 ⟨subd20_3_71, List.forall_mem_cons.2 ⟨subd20_3_72, List.forall_mem_cons.2 ⟨subd20_3_73, List.forall_mem_cons.2 ⟨subd20_3_74, List.forall_mem_cons.2 ⟨subd20_3_75, List.forall_mem_cons.2 ⟨subd20_3_76, List.forall_mem_cons.2 ⟨subd20_3_77, List.forall_mem_cons.2 ⟨subd20_3_78, List.forall_mem_cons.2 ⟨subd20_3_79, List.forall_mem_cons.2 ⟨subd20_3_80, List.forall_mem_cons.2 ⟨subd20_3_81, List.forall_mem_cons.2 ⟨subd20_3_82, List.forall_mem_cons.2 ⟨subd20_3_83, List.forall_mem_cons.2 ⟨subd20_3_84, List.forall_mem_cons.2 ⟨subd20_3_85, List.forall_mem_cons.2 ⟨subd20_3_86, List.forall_mem_cons.2 ⟨subd20_3_87, List.forall_mem_cons.2 ⟨subd20_3_88, List.forall_mem_cons.2 ⟨subd20_3_89, List.forall_mem_cons.2 ⟨subd20_3_90, List.forall_mem_cons.2 ⟨subd20_3_91, List.forall_mem_cons.2 ⟨subd20_3_92, List.forall_mem_cons.2 ⟨subd20_3_93, List.forall_mem_cons.2 ⟨subd20_3_94, List.forall_mem_cons.2 ⟨subd20_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
