import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_2_64 : subd4_2 [1, 5] = true := by decide +kernel
theorem subd4_2_65 : subd4_2 [2, -5] = true := by decide +kernel
theorem subd4_2_66 : subd4_2 [2, -4] = true := by decide +kernel
theorem subd4_2_67 : subd4_2 [2, -3] = true := by decide +kernel
theorem subd4_2_68 : subd4_2 [2, -2] = true := by decide +kernel
theorem subd4_2_69 : subd4_2 [2, -1] = true := by decide +kernel
theorem subd4_2_70 : subd4_2 [2, 0] = true := by decide +kernel
theorem subd4_2_71 : subd4_2 [2, 1] = true := by decide +kernel
theorem subd4_2_72 : subd4_2 [2, 2] = true := by decide +kernel
theorem subd4_2_73 : subd4_2 [2, 3] = true := by decide +kernel
theorem subd4_2_74 : subd4_2 [2, 4] = true := by decide +kernel
theorem subd4_2_75 : subd4_2 [2, 5] = true := by decide +kernel
theorem subd4_2_76 : subd4_2 [3, -4] = true := by decide +kernel
theorem subd4_2_77 : subd4_2 [3, -3] = true := by decide +kernel
theorem subd4_2_78 : subd4_2 [3, -2] = true := by decide +kernel
theorem subd4_2_79 : subd4_2 [3, -1] = true := by decide +kernel
theorem subd4_2_80 : subd4_2 [3, 0] = true := by decide +kernel
theorem subd4_2_81 : subd4_2 [3, 1] = true := by decide +kernel
theorem subd4_2_82 : subd4_2 [3, 2] = true := by decide +kernel
theorem subd4_2_83 : subd4_2 [3, 3] = true := by decide +kernel
theorem subd4_2_84 : subd4_2 [3, 4] = true := by decide +kernel
theorem subd4_2_85 : subd4_2 [3, 5] = true := by decide +kernel
theorem subd4_2_86 : subd4_2 [4, -3] = true := by decide +kernel
theorem subd4_2_87 : subd4_2 [4, -2] = true := by decide +kernel
theorem subd4_2_88 : subd4_2 [4, -1] = true := by decide +kernel
theorem subd4_2_89 : subd4_2 [4, 0] = true := by decide +kernel
theorem subd4_2_90 : subd4_2 [4, 1] = true := by decide +kernel
theorem subd4_2_91 : subd4_2 [4, 2] = true := by decide +kernel
theorem subd4_2_92 : subd4_2 [4, 3] = true := by decide +kernel
theorem subd4_2_93 : subd4_2 [4, 4] = true := by decide +kernel
theorem sbd4_2_2 : ∀ q ∈ blkd4_2_2, subd4_2 q = true := by
  unfold blkd4_2_2
  exact List.forall_mem_cons.2 ⟨subd4_2_64, List.forall_mem_cons.2 ⟨subd4_2_65, List.forall_mem_cons.2 ⟨subd4_2_66, List.forall_mem_cons.2 ⟨subd4_2_67, List.forall_mem_cons.2 ⟨subd4_2_68, List.forall_mem_cons.2 ⟨subd4_2_69, List.forall_mem_cons.2 ⟨subd4_2_70, List.forall_mem_cons.2 ⟨subd4_2_71, List.forall_mem_cons.2 ⟨subd4_2_72, List.forall_mem_cons.2 ⟨subd4_2_73, List.forall_mem_cons.2 ⟨subd4_2_74, List.forall_mem_cons.2 ⟨subd4_2_75, List.forall_mem_cons.2 ⟨subd4_2_76, List.forall_mem_cons.2 ⟨subd4_2_77, List.forall_mem_cons.2 ⟨subd4_2_78, List.forall_mem_cons.2 ⟨subd4_2_79, List.forall_mem_cons.2 ⟨subd4_2_80, List.forall_mem_cons.2 ⟨subd4_2_81, List.forall_mem_cons.2 ⟨subd4_2_82, List.forall_mem_cons.2 ⟨subd4_2_83, List.forall_mem_cons.2 ⟨subd4_2_84, List.forall_mem_cons.2 ⟨subd4_2_85, List.forall_mem_cons.2 ⟨subd4_2_86, List.forall_mem_cons.2 ⟨subd4_2_87, List.forall_mem_cons.2 ⟨subd4_2_88, List.forall_mem_cons.2 ⟨subd4_2_89, List.forall_mem_cons.2 ⟨subd4_2_90, List.forall_mem_cons.2 ⟨subd4_2_91, List.forall_mem_cons.2 ⟨subd4_2_92, List.forall_mem_cons.2 ⟨subd4_2_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-5] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-4, -5] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-4, -4] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-4, -3] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-4, -2] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-4, -1] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-4, 0] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [-4, 1] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [-4, 2] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [-4, 3] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [-3, -6] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [-3, -5] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [-3, -4] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [-3, -3] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [-3, -2] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [-3, -1] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [-3, 0] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [-3, 1] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [-3, 2] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [-3, 3] = true := by decide +kernel
theorem subd4_3_20 : subd4_3 [-3, 4] = true := by decide +kernel
theorem subd4_3_21 : subd4_3 [-2, -6] = true := by decide +kernel
theorem subd4_3_22 : subd4_3 [-2, -5] = true := by decide +kernel
theorem subd4_3_23 : subd4_3 [-2, -4] = true := by decide +kernel
theorem subd4_3_24 : subd4_3 [-2, -3] = true := by decide +kernel
theorem subd4_3_25 : subd4_3 [-2, -2] = true := by decide +kernel
theorem subd4_3_26 : subd4_3 [-2, -1] = true := by decide +kernel
theorem subd4_3_27 : subd4_3 [-2, 0] = true := by decide +kernel
theorem subd4_3_28 : subd4_3 [-2, 1] = true := by decide +kernel
theorem subd4_3_29 : subd4_3 [-2, 2] = true := by decide +kernel
theorem subd4_3_30 : subd4_3 [-2, 3] = true := by decide +kernel
theorem subd4_3_31 : subd4_3 [-2, 4] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_cons.2 ⟨subd4_3_20, List.forall_mem_cons.2 ⟨subd4_3_21, List.forall_mem_cons.2 ⟨subd4_3_22, List.forall_mem_cons.2 ⟨subd4_3_23, List.forall_mem_cons.2 ⟨subd4_3_24, List.forall_mem_cons.2 ⟨subd4_3_25, List.forall_mem_cons.2 ⟨subd4_3_26, List.forall_mem_cons.2 ⟨subd4_3_27, List.forall_mem_cons.2 ⟨subd4_3_28, List.forall_mem_cons.2 ⟨subd4_3_29, List.forall_mem_cons.2 ⟨subd4_3_30, List.forall_mem_cons.2 ⟨subd4_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_32 : subd4_3 [-1, -6] = true := by decide +kernel
theorem subd4_3_33 : subd4_3 [-1, -5] = true := by decide +kernel
theorem subd4_3_34 : subd4_3 [-1, -4] = true := by decide +kernel
theorem subd4_3_35 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_36 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_37 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_38 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_39 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_40 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_41 : subd4_3 [-1, 3] = true := by decide +kernel
theorem subd4_3_42 : subd4_3 [-1, 4] = true := by decide +kernel
theorem subd4_3_43 : subd4_3 [-1, 5] = true := by decide +kernel
theorem subd4_3_44 : subd4_3 [0, -6] = true := by decide +kernel
theorem subd4_3_45 : subd4_3 [0, -5] = true := by decide +kernel
theorem subd4_3_46 : subd4_3 [0, -4] = true := by decide +kernel
theorem subd4_3_47 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_48 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_49 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_50 : subd4_3 [0, 0] = true := by decide +kernel
theorem subd4_3_51 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_52 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_53 : subd4_3 [0, 3] = true := by decide +kernel
theorem subd4_3_54 : subd4_3 [0, 4] = true := by decide +kernel
theorem subd4_3_55 : subd4_3 [0, 5] = true := by decide +kernel
theorem subd4_3_56 : subd4_3 [1, -6] = true := by decide +kernel
theorem subd4_3_57 : subd4_3 [1, -5] = true := by decide +kernel
theorem subd4_3_58 : subd4_3 [1, -4] = true := by decide +kernel
theorem subd4_3_59 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_60 : subd4_3 [1, -2] = true := by decide +kernel
theorem subd4_3_61 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_62 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_63 : subd4_3 [1, 1] = true := by decide +kernel
theorem sbd4_3_1 : ∀ q ∈ blkd4_3_1, subd4_3 q = true := by
  unfold blkd4_3_1
  exact List.forall_mem_cons.2 ⟨subd4_3_32, List.forall_mem_cons.2 ⟨subd4_3_33, List.forall_mem_cons.2 ⟨subd4_3_34, List.forall_mem_cons.2 ⟨subd4_3_35, List.forall_mem_cons.2 ⟨subd4_3_36, List.forall_mem_cons.2 ⟨subd4_3_37, List.forall_mem_cons.2 ⟨subd4_3_38, List.forall_mem_cons.2 ⟨subd4_3_39, List.forall_mem_cons.2 ⟨subd4_3_40, List.forall_mem_cons.2 ⟨subd4_3_41, List.forall_mem_cons.2 ⟨subd4_3_42, List.forall_mem_cons.2 ⟨subd4_3_43, List.forall_mem_cons.2 ⟨subd4_3_44, List.forall_mem_cons.2 ⟨subd4_3_45, List.forall_mem_cons.2 ⟨subd4_3_46, List.forall_mem_cons.2 ⟨subd4_3_47, List.forall_mem_cons.2 ⟨subd4_3_48, List.forall_mem_cons.2 ⟨subd4_3_49, List.forall_mem_cons.2 ⟨subd4_3_50, List.forall_mem_cons.2 ⟨subd4_3_51, List.forall_mem_cons.2 ⟨subd4_3_52, List.forall_mem_cons.2 ⟨subd4_3_53, List.forall_mem_cons.2 ⟨subd4_3_54, List.forall_mem_cons.2 ⟨subd4_3_55, List.forall_mem_cons.2 ⟨subd4_3_56, List.forall_mem_cons.2 ⟨subd4_3_57, List.forall_mem_cons.2 ⟨subd4_3_58, List.forall_mem_cons.2 ⟨subd4_3_59, List.forall_mem_cons.2 ⟨subd4_3_60, List.forall_mem_cons.2 ⟨subd4_3_61, List.forall_mem_cons.2 ⟨subd4_3_62, List.forall_mem_cons.2 ⟨subd4_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
