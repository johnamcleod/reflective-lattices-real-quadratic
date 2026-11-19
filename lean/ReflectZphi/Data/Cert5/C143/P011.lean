import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_32 : subd12_0 [-1, -4] = true := by decide +kernel
theorem subd12_0_33 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_34 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_35 : subd12_0 [-1, -1] = true := by decide +kernel
theorem subd12_0_36 : subd12_0 [-1, 0] = true := by decide +kernel
theorem subd12_0_37 : subd12_0 [-1, 1] = true := by decide +kernel
theorem subd12_0_38 : subd12_0 [-1, 2] = true := by decide +kernel
theorem subd12_0_39 : subd12_0 [-1, 3] = true := by decide +kernel
theorem subd12_0_40 : subd12_0 [-1, 4] = true := by decide +kernel
theorem subd12_0_41 : subd12_0 [-1, 5] = true := by decide +kernel
theorem subd12_0_42 : subd12_0 [0, -6] = true := by decide +kernel
theorem subd12_0_43 : subd12_0 [0, -5] = true := by decide +kernel
theorem subd12_0_44 : subd12_0 [0, -4] = true := by decide +kernel
theorem subd12_0_45 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_46 : subd12_0 [0, -2] = true := by decide +kernel
theorem subd12_0_47 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_48 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_49 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_50 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_51 : subd12_0 [0, 3] = true := by decide +kernel
theorem subd12_0_52 : subd12_0 [0, 4] = true := by decide +kernel
theorem subd12_0_53 : subd12_0 [0, 5] = true := by decide +kernel
theorem subd12_0_54 : subd12_0 [1, -6] = true := by decide +kernel
theorem subd12_0_55 : subd12_0 [1, -5] = true := by decide +kernel
theorem subd12_0_56 : subd12_0 [1, -4] = true := by decide +kernel
theorem subd12_0_57 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_58 : subd12_0 [1, -2] = true := by decide +kernel
theorem subd12_0_59 : subd12_0 [1, -1] = true := by decide +kernel
theorem subd12_0_60 : subd12_0 [1, 0] = true := by decide +kernel
theorem subd12_0_61 : subd12_0 [1, 1] = true := by decide +kernel
theorem subd12_0_62 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_63 : subd12_0 [1, 3] = true := by decide +kernel
theorem sbd12_0_1 : ∀ q ∈ blkd12_0_1, subd12_0 q = true := by
  unfold blkd12_0_1
  exact List.forall_mem_cons.2 ⟨subd12_0_32, List.forall_mem_cons.2 ⟨subd12_0_33, List.forall_mem_cons.2 ⟨subd12_0_34, List.forall_mem_cons.2 ⟨subd12_0_35, List.forall_mem_cons.2 ⟨subd12_0_36, List.forall_mem_cons.2 ⟨subd12_0_37, List.forall_mem_cons.2 ⟨subd12_0_38, List.forall_mem_cons.2 ⟨subd12_0_39, List.forall_mem_cons.2 ⟨subd12_0_40, List.forall_mem_cons.2 ⟨subd12_0_41, List.forall_mem_cons.2 ⟨subd12_0_42, List.forall_mem_cons.2 ⟨subd12_0_43, List.forall_mem_cons.2 ⟨subd12_0_44, List.forall_mem_cons.2 ⟨subd12_0_45, List.forall_mem_cons.2 ⟨subd12_0_46, List.forall_mem_cons.2 ⟨subd12_0_47, List.forall_mem_cons.2 ⟨subd12_0_48, List.forall_mem_cons.2 ⟨subd12_0_49, List.forall_mem_cons.2 ⟨subd12_0_50, List.forall_mem_cons.2 ⟨subd12_0_51, List.forall_mem_cons.2 ⟨subd12_0_52, List.forall_mem_cons.2 ⟨subd12_0_53, List.forall_mem_cons.2 ⟨subd12_0_54, List.forall_mem_cons.2 ⟨subd12_0_55, List.forall_mem_cons.2 ⟨subd12_0_56, List.forall_mem_cons.2 ⟨subd12_0_57, List.forall_mem_cons.2 ⟨subd12_0_58, List.forall_mem_cons.2 ⟨subd12_0_59, List.forall_mem_cons.2 ⟨subd12_0_60, List.forall_mem_cons.2 ⟨subd12_0_61, List.forall_mem_cons.2 ⟨subd12_0_62, List.forall_mem_cons.2 ⟨subd12_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_64 : subd12_0 [1, 4] = true := by decide +kernel
theorem subd12_0_65 : subd12_0 [1, 5] = true := by decide +kernel
theorem subd12_0_66 : subd12_0 [2, -5] = true := by decide +kernel
theorem subd12_0_67 : subd12_0 [2, -4] = true := by decide +kernel
theorem subd12_0_68 : subd12_0 [2, -3] = true := by decide +kernel
theorem subd12_0_69 : subd12_0 [2, -2] = true := by decide +kernel
theorem subd12_0_70 : subd12_0 [2, -1] = true := by decide +kernel
theorem subd12_0_71 : subd12_0 [2, 0] = true := by decide +kernel
theorem subd12_0_72 : subd12_0 [2, 1] = true := by decide +kernel
theorem subd12_0_73 : subd12_0 [2, 2] = true := by decide +kernel
theorem subd12_0_74 : subd12_0 [2, 3] = true := by decide +kernel
theorem subd12_0_75 : subd12_0 [2, 4] = true := by decide +kernel
theorem subd12_0_76 : subd12_0 [2, 5] = true := by decide +kernel
theorem subd12_0_77 : subd12_0 [3, -5] = true := by decide +kernel
theorem subd12_0_78 : subd12_0 [3, -4] = true := by decide +kernel
theorem subd12_0_79 : subd12_0 [3, -3] = true := by decide +kernel
theorem subd12_0_80 : subd12_0 [3, -2] = true := by decide +kernel
theorem subd12_0_81 : subd12_0 [3, -1] = true := by decide +kernel
theorem subd12_0_82 : subd12_0 [3, 0] = true := by decide +kernel
theorem subd12_0_83 : subd12_0 [3, 1] = true := by decide +kernel
theorem subd12_0_84 : subd12_0 [3, 2] = true := by decide +kernel
theorem subd12_0_85 : subd12_0 [3, 3] = true := by decide +kernel
theorem subd12_0_86 : subd12_0 [3, 4] = true := by decide +kernel
theorem subd12_0_87 : subd12_0 [4, -4] = true := by decide +kernel
theorem subd12_0_88 : subd12_0 [4, -3] = true := by decide +kernel
theorem subd12_0_89 : subd12_0 [4, -2] = true := by decide +kernel
theorem subd12_0_90 : subd12_0 [4, -1] = true := by decide +kernel
theorem subd12_0_91 : subd12_0 [4, 0] = true := by decide +kernel
theorem subd12_0_92 : subd12_0 [4, 1] = true := by decide +kernel
theorem subd12_0_93 : subd12_0 [4, 2] = true := by decide +kernel
theorem subd12_0_94 : subd12_0 [4, 3] = true := by decide +kernel
theorem subd12_0_95 : subd12_0 [5] = true := by decide +kernel
theorem sbd12_0_2 : ∀ q ∈ blkd12_0_2, subd12_0 q = true := by
  unfold blkd12_0_2
  exact List.forall_mem_cons.2 ⟨subd12_0_64, List.forall_mem_cons.2 ⟨subd12_0_65, List.forall_mem_cons.2 ⟨subd12_0_66, List.forall_mem_cons.2 ⟨subd12_0_67, List.forall_mem_cons.2 ⟨subd12_0_68, List.forall_mem_cons.2 ⟨subd12_0_69, List.forall_mem_cons.2 ⟨subd12_0_70, List.forall_mem_cons.2 ⟨subd12_0_71, List.forall_mem_cons.2 ⟨subd12_0_72, List.forall_mem_cons.2 ⟨subd12_0_73, List.forall_mem_cons.2 ⟨subd12_0_74, List.forall_mem_cons.2 ⟨subd12_0_75, List.forall_mem_cons.2 ⟨subd12_0_76, List.forall_mem_cons.2 ⟨subd12_0_77, List.forall_mem_cons.2 ⟨subd12_0_78, List.forall_mem_cons.2 ⟨subd12_0_79, List.forall_mem_cons.2 ⟨subd12_0_80, List.forall_mem_cons.2 ⟨subd12_0_81, List.forall_mem_cons.2 ⟨subd12_0_82, List.forall_mem_cons.2 ⟨subd12_0_83, List.forall_mem_cons.2 ⟨subd12_0_84, List.forall_mem_cons.2 ⟨subd12_0_85, List.forall_mem_cons.2 ⟨subd12_0_86, List.forall_mem_cons.2 ⟨subd12_0_87, List.forall_mem_cons.2 ⟨subd12_0_88, List.forall_mem_cons.2 ⟨subd12_0_89, List.forall_mem_cons.2 ⟨subd12_0_90, List.forall_mem_cons.2 ⟨subd12_0_91, List.forall_mem_cons.2 ⟨subd12_0_92, List.forall_mem_cons.2 ⟨subd12_0_93, List.forall_mem_cons.2 ⟨subd12_0_94, List.forall_mem_cons.2 ⟨subd12_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-5] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-4, -4] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-4, -3] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-4, -2] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-4, -1] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-4, 0] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-4, 1] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-4, 2] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-4, 3] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-3, -5] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [-3, -4] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [-3, -3] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [-3, -2] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [-3, -1] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [-3, 0] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [-3, 1] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [-3, 2] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [-3, 3] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [-3, 4] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [-2, -6] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [-2, -5] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [-2, -4] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [-2, -3] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [-2, -2] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [-2, -1] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [-2, 0] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [-2, 1] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [-2, 2] = true := by decide +kernel
theorem subd12_1_28 : subd12_1 [-2, 3] = true := by decide +kernel
theorem subd12_1_29 : subd12_1 [-2, 4] = true := by decide +kernel
theorem subd12_1_30 : subd12_1 [-1, -6] = true := by decide +kernel
theorem subd12_1_31 : subd12_1 [-1, -5] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_cons.2 ⟨subd12_1_28, List.forall_mem_cons.2 ⟨subd12_1_29, List.forall_mem_cons.2 ⟨subd12_1_30, List.forall_mem_cons.2 ⟨subd12_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
