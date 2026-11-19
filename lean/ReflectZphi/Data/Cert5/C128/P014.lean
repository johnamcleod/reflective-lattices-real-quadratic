import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_3_64 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_65 : subd4_3 [1, 3] = true := by decide +kernel
theorem subd4_3_66 : subd4_3 [1, 4] = true := by decide +kernel
theorem subd4_3_67 : subd4_3 [1, 5] = true := by decide +kernel
theorem subd4_3_68 : subd4_3 [2, -5] = true := by decide +kernel
theorem subd4_3_69 : subd4_3 [2, -4] = true := by decide +kernel
theorem subd4_3_70 : subd4_3 [2, -3] = true := by decide +kernel
theorem subd4_3_71 : subd4_3 [2, -2] = true := by decide +kernel
theorem subd4_3_72 : subd4_3 [2, -1] = true := by decide +kernel
theorem subd4_3_73 : subd4_3 [2, 0] = true := by decide +kernel
theorem subd4_3_74 : subd4_3 [2, 1] = true := by decide +kernel
theorem subd4_3_75 : subd4_3 [2, 2] = true := by decide +kernel
theorem subd4_3_76 : subd4_3 [2, 3] = true := by decide +kernel
theorem subd4_3_77 : subd4_3 [2, 4] = true := by decide +kernel
theorem subd4_3_78 : subd4_3 [2, 5] = true := by decide +kernel
theorem subd4_3_79 : subd4_3 [3, -5] = true := by decide +kernel
theorem subd4_3_80 : subd4_3 [3, -4] = true := by decide +kernel
theorem subd4_3_81 : subd4_3 [3, -3] = true := by decide +kernel
theorem subd4_3_82 : subd4_3 [3, -2] = true := by decide +kernel
theorem subd4_3_83 : subd4_3 [3, -1] = true := by decide +kernel
theorem subd4_3_84 : subd4_3 [3, 0] = true := by decide +kernel
theorem subd4_3_85 : subd4_3 [3, 1] = true := by decide +kernel
theorem subd4_3_86 : subd4_3 [3, 2] = true := by decide +kernel
theorem subd4_3_87 : subd4_3 [3, 3] = true := by decide +kernel
theorem subd4_3_88 : subd4_3 [3, 4] = true := by decide +kernel
theorem subd4_3_89 : subd4_3 [3, 5] = true := by decide +kernel
theorem subd4_3_90 : subd4_3 [4, -4] = true := by decide +kernel
theorem subd4_3_91 : subd4_3 [4, -3] = true := by decide +kernel
theorem subd4_3_92 : subd4_3 [4, -2] = true := by decide +kernel
theorem subd4_3_93 : subd4_3 [4, -1] = true := by decide +kernel
theorem subd4_3_94 : subd4_3 [4, 0] = true := by decide +kernel
theorem subd4_3_95 : subd4_3 [4, 1] = true := by decide +kernel
theorem sbd4_3_2 : ∀ q ∈ blkd4_3_2, subd4_3 q = true := by
  unfold blkd4_3_2
  exact List.forall_mem_cons.2 ⟨subd4_3_64, List.forall_mem_cons.2 ⟨subd4_3_65, List.forall_mem_cons.2 ⟨subd4_3_66, List.forall_mem_cons.2 ⟨subd4_3_67, List.forall_mem_cons.2 ⟨subd4_3_68, List.forall_mem_cons.2 ⟨subd4_3_69, List.forall_mem_cons.2 ⟨subd4_3_70, List.forall_mem_cons.2 ⟨subd4_3_71, List.forall_mem_cons.2 ⟨subd4_3_72, List.forall_mem_cons.2 ⟨subd4_3_73, List.forall_mem_cons.2 ⟨subd4_3_74, List.forall_mem_cons.2 ⟨subd4_3_75, List.forall_mem_cons.2 ⟨subd4_3_76, List.forall_mem_cons.2 ⟨subd4_3_77, List.forall_mem_cons.2 ⟨subd4_3_78, List.forall_mem_cons.2 ⟨subd4_3_79, List.forall_mem_cons.2 ⟨subd4_3_80, List.forall_mem_cons.2 ⟨subd4_3_81, List.forall_mem_cons.2 ⟨subd4_3_82, List.forall_mem_cons.2 ⟨subd4_3_83, List.forall_mem_cons.2 ⟨subd4_3_84, List.forall_mem_cons.2 ⟨subd4_3_85, List.forall_mem_cons.2 ⟨subd4_3_86, List.forall_mem_cons.2 ⟨subd4_3_87, List.forall_mem_cons.2 ⟨subd4_3_88, List.forall_mem_cons.2 ⟨subd4_3_89, List.forall_mem_cons.2 ⟨subd4_3_90, List.forall_mem_cons.2 ⟨subd4_3_91, List.forall_mem_cons.2 ⟨subd4_3_92, List.forall_mem_cons.2 ⟨subd4_3_93, List.forall_mem_cons.2 ⟨subd4_3_94, List.forall_mem_cons.2 ⟨subd4_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_96 : subd4_3 [4, 2] = true := by decide +kernel
theorem subd4_3_97 : subd4_3 [4, 3] = true := by decide +kernel
theorem subd4_3_98 : subd4_3 [4, 4] = true := by decide +kernel
theorem subd4_3_99 : subd4_3 [5] = true := by decide +kernel
theorem sbd4_3_3 : ∀ q ∈ blkd4_3_3, subd4_3 q = true := by
  unfold blkd4_3_3
  exact List.forall_mem_cons.2 ⟨subd4_3_96, List.forall_mem_cons.2 ⟨subd4_3_97, List.forall_mem_cons.2 ⟨subd4_3_98, List.forall_mem_cons.2 ⟨subd4_3_99, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-5] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-4, -4] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-4, -3] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-4, -2] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-4, -1] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-4, 0] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [-4, 1] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [-4, 2] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [-4, 3] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [-4, 4] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [-3, -5] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [-3, -4] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [-3, -3] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [-3, -2] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [-3, -1] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [-3, 0] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [-3, 1] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [-3, 2] = true := by decide +kernel
theorem subd4_4_18 : subd4_4 [-3, 3] = true := by decide +kernel
theorem subd4_4_19 : subd4_4 [-3, 4] = true := by decide +kernel
theorem subd4_4_20 : subd4_4 [-3, 5] = true := by decide +kernel
theorem subd4_4_21 : subd4_4 [-2, -6] = true := by decide +kernel
theorem subd4_4_22 : subd4_4 [-2, -5] = true := by decide +kernel
theorem subd4_4_23 : subd4_4 [-2, -4] = true := by decide +kernel
theorem subd4_4_24 : subd4_4 [-2, -3] = true := by decide +kernel
theorem subd4_4_25 : subd4_4 [-2, -2] = true := by decide +kernel
theorem subd4_4_26 : subd4_4 [-2, -1] = true := by decide +kernel
theorem subd4_4_27 : subd4_4 [-2, 0] = true := by decide +kernel
theorem subd4_4_28 : subd4_4 [-2, 1] = true := by decide +kernel
theorem subd4_4_29 : subd4_4 [-2, 2] = true := by decide +kernel
theorem subd4_4_30 : subd4_4 [-2, 3] = true := by decide +kernel
theorem subd4_4_31 : subd4_4 [-2, 4] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_cons.2 ⟨subd4_4_18, List.forall_mem_cons.2 ⟨subd4_4_19, List.forall_mem_cons.2 ⟨subd4_4_20, List.forall_mem_cons.2 ⟨subd4_4_21, List.forall_mem_cons.2 ⟨subd4_4_22, List.forall_mem_cons.2 ⟨subd4_4_23, List.forall_mem_cons.2 ⟨subd4_4_24, List.forall_mem_cons.2 ⟨subd4_4_25, List.forall_mem_cons.2 ⟨subd4_4_26, List.forall_mem_cons.2 ⟨subd4_4_27, List.forall_mem_cons.2 ⟨subd4_4_28, List.forall_mem_cons.2 ⟨subd4_4_29, List.forall_mem_cons.2 ⟨subd4_4_30, List.forall_mem_cons.2 ⟨subd4_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_32 : subd4_4 [-2, 5] = true := by decide +kernel
theorem subd4_4_33 : subd4_4 [-1, -6] = true := by decide +kernel
theorem subd4_4_34 : subd4_4 [-1, -5] = true := by decide +kernel
theorem subd4_4_35 : subd4_4 [-1, -4] = true := by decide +kernel
theorem subd4_4_36 : subd4_4 [-1, -3] = true := by decide +kernel
theorem subd4_4_37 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_38 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_39 : subd4_4 [-1, 0] = true := by decide +kernel
theorem subd4_4_40 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_41 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_42 : subd4_4 [-1, 3] = true := by decide +kernel
theorem subd4_4_43 : subd4_4 [-1, 4] = true := by decide +kernel
theorem subd4_4_44 : subd4_4 [-1, 5] = true := by decide +kernel
theorem subd4_4_45 : subd4_4 [-1, 6] = true := by decide +kernel
theorem subd4_4_46 : subd4_4 [0, -6] = true := by decide +kernel
theorem subd4_4_47 : subd4_4 [0, -5] = true := by decide +kernel
theorem subd4_4_48 : subd4_4 [0, -4] = true := by decide +kernel
theorem subd4_4_49 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_50 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_51 : subd4_4 [0, -1] = true := by decide +kernel
theorem subd4_4_52 : subd4_4 [0, 0] = true := by decide +kernel
theorem subd4_4_53 : subd4_4 [0, 1] = true := by decide +kernel
theorem subd4_4_54 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_55 : subd4_4 [0, 3] = true := by decide +kernel
theorem subd4_4_56 : subd4_4 [0, 4] = true := by decide +kernel
theorem subd4_4_57 : subd4_4 [0, 5] = true := by decide +kernel
theorem subd4_4_58 : subd4_4 [1, -7] = true := by decide +kernel
theorem subd4_4_59 : subd4_4 [1, -6] = true := by decide +kernel
theorem subd4_4_60 : subd4_4 [1, -5] = true := by decide +kernel
theorem subd4_4_61 : subd4_4 [1, -4] = true := by decide +kernel
theorem subd4_4_62 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_63 : subd4_4 [1, -2] = true := by decide +kernel
theorem sbd4_4_1 : ∀ q ∈ blkd4_4_1, subd4_4 q = true := by
  unfold blkd4_4_1
  exact List.forall_mem_cons.2 ⟨subd4_4_32, List.forall_mem_cons.2 ⟨subd4_4_33, List.forall_mem_cons.2 ⟨subd4_4_34, List.forall_mem_cons.2 ⟨subd4_4_35, List.forall_mem_cons.2 ⟨subd4_4_36, List.forall_mem_cons.2 ⟨subd4_4_37, List.forall_mem_cons.2 ⟨subd4_4_38, List.forall_mem_cons.2 ⟨subd4_4_39, List.forall_mem_cons.2 ⟨subd4_4_40, List.forall_mem_cons.2 ⟨subd4_4_41, List.forall_mem_cons.2 ⟨subd4_4_42, List.forall_mem_cons.2 ⟨subd4_4_43, List.forall_mem_cons.2 ⟨subd4_4_44, List.forall_mem_cons.2 ⟨subd4_4_45, List.forall_mem_cons.2 ⟨subd4_4_46, List.forall_mem_cons.2 ⟨subd4_4_47, List.forall_mem_cons.2 ⟨subd4_4_48, List.forall_mem_cons.2 ⟨subd4_4_49, List.forall_mem_cons.2 ⟨subd4_4_50, List.forall_mem_cons.2 ⟨subd4_4_51, List.forall_mem_cons.2 ⟨subd4_4_52, List.forall_mem_cons.2 ⟨subd4_4_53, List.forall_mem_cons.2 ⟨subd4_4_54, List.forall_mem_cons.2 ⟨subd4_4_55, List.forall_mem_cons.2 ⟨subd4_4_56, List.forall_mem_cons.2 ⟨subd4_4_57, List.forall_mem_cons.2 ⟨subd4_4_58, List.forall_mem_cons.2 ⟨subd4_4_59, List.forall_mem_cons.2 ⟨subd4_4_60, List.forall_mem_cons.2 ⟨subd4_4_61, List.forall_mem_cons.2 ⟨subd4_4_62, List.forall_mem_cons.2 ⟨subd4_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
