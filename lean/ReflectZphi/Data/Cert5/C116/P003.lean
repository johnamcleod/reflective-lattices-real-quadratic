import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_1_96 : subd4_1 [4, -4] = true := by decide +kernel
theorem subd4_1_97 : subd4_1 [4, -3] = true := by decide +kernel
theorem subd4_1_98 : subd4_1 [4, -2] = true := by decide +kernel
theorem subd4_1_99 : subd4_1 [4, -1] = true := by decide +kernel
theorem subd4_1_100 : subd4_1 [4, 0] = true := by decide +kernel
theorem subd4_1_101 : subd4_1 [4, 1] = true := by decide +kernel
theorem subd4_1_102 : subd4_1 [4, 2] = true := by decide +kernel
theorem subd4_1_103 : subd4_1 [5] = true := by decide +kernel
theorem sbd4_1_3 : ∀ q ∈ blkd4_1_3, subd4_1 q = true := by
  unfold blkd4_1_3
  exact List.forall_mem_cons.2 ⟨subd4_1_96, List.forall_mem_cons.2 ⟨subd4_1_97, List.forall_mem_cons.2 ⟨subd4_1_98, List.forall_mem_cons.2 ⟨subd4_1_99, List.forall_mem_cons.2 ⟨subd4_1_100, List.forall_mem_cons.2 ⟨subd4_1_101, List.forall_mem_cons.2 ⟨subd4_1_102, List.forall_mem_cons.2 ⟨subd4_1_103, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [1, 1] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-8] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-7, -6] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-7, -5] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-7, -4] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-7, -3] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-7, -2] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-7, -1] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-7, 0] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-7, 1] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-7, 2] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-6, -7] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-6, -6] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-6, -5] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-6, -4] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-6, -3] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [-6, -2] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [-6, -1] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [-6, 0] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [-6, 1] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [-6, 2] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [-6, 3] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [-5, -7] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [-5, -6] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [-5, -5] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [-5, -4] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [-5, -3] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [-5, -2] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [-5, -1] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [-5, 0] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [-5, 1] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [-5, 2] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [-5, 3] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [-5, 4] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [-4, -8] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [-4, -7] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [-4, -6] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [-4, -5] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [-4, -4] = true := by decide +kernel
theorem subd5_1_38 : subd5_1 [-4, -3] = true := by decide +kernel
theorem subd5_1_39 : subd5_1 [-4, -2] = true := by decide +kernel
theorem subd5_1_40 : subd5_1 [-4, -1] = true := by decide +kernel
theorem subd5_1_41 : subd5_1 [-4, 0] = true := by decide +kernel
theorem subd5_1_42 : subd5_1 [-4, 1] = true := by decide +kernel
theorem subd5_1_43 : subd5_1 [-4, 2] = true := by decide +kernel
theorem subd5_1_44 : subd5_1 [-4, 3] = true := by decide +kernel
theorem subd5_1_45 : subd5_1 [-4, 4] = true := by decide +kernel
theorem subd5_1_46 : subd5_1 [-4, 5] = true := by decide +kernel
theorem subd5_1_47 : subd5_1 [-3, -8] = true := by decide +kernel
theorem subd5_1_48 : subd5_1 [-3, -7] = true := by decide +kernel
theorem subd5_1_49 : subd5_1 [-3, -6] = true := by decide +kernel
theorem subd5_1_50 : subd5_1 [-3, -5] = true := by decide +kernel
theorem subd5_1_51 : subd5_1 [-3, -4] = true := by decide +kernel
theorem subd5_1_52 : subd5_1 [-3, -3] = true := by decide +kernel
theorem subd5_1_53 : subd5_1 [-3, -2, -6] = true := by decide +kernel
theorem subd5_1_54 : subd5_1 [-3, -2, -5] = true := by decide +kernel
theorem subd5_1_55 : subd5_1 [-3, -2, -4] = true := by decide +kernel
theorem subd5_1_56 : subd5_1 [-3, -2, -3] = true := by decide +kernel
theorem subd5_1_57 : subd5_1 [-3, -2, -2] = true := by decide +kernel
theorem subd5_1_58 : subd5_1 [-3, -2, -1] = true := by decide +kernel
theorem subd5_1_59 : subd5_1 [-3, -2, 0] = true := by decide +kernel
theorem subd5_1_60 : subd5_1 [-3, -2, 1] = true := by decide +kernel
theorem subd5_1_61 : subd5_1 [-3, -2, 2] = true := by decide +kernel
theorem subd5_1_62 : subd5_1 [-3, -2, 3] = true := by decide +kernel
theorem subd5_1_63 : subd5_1 [-3, -2, 4] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_cons.2 ⟨subd5_1_38, List.forall_mem_cons.2 ⟨subd5_1_39, List.forall_mem_cons.2 ⟨subd5_1_40, List.forall_mem_cons.2 ⟨subd5_1_41, List.forall_mem_cons.2 ⟨subd5_1_42, List.forall_mem_cons.2 ⟨subd5_1_43, List.forall_mem_cons.2 ⟨subd5_1_44, List.forall_mem_cons.2 ⟨subd5_1_45, List.forall_mem_cons.2 ⟨subd5_1_46, List.forall_mem_cons.2 ⟨subd5_1_47, List.forall_mem_cons.2 ⟨subd5_1_48, List.forall_mem_cons.2 ⟨subd5_1_49, List.forall_mem_cons.2 ⟨subd5_1_50, List.forall_mem_cons.2 ⟨subd5_1_51, List.forall_mem_cons.2 ⟨subd5_1_52, List.forall_mem_cons.2 ⟨subd5_1_53, List.forall_mem_cons.2 ⟨subd5_1_54, List.forall_mem_cons.2 ⟨subd5_1_55, List.forall_mem_cons.2 ⟨subd5_1_56, List.forall_mem_cons.2 ⟨subd5_1_57, List.forall_mem_cons.2 ⟨subd5_1_58, List.forall_mem_cons.2 ⟨subd5_1_59, List.forall_mem_cons.2 ⟨subd5_1_60, List.forall_mem_cons.2 ⟨subd5_1_61, List.forall_mem_cons.2 ⟨subd5_1_62, List.forall_mem_cons.2 ⟨subd5_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_64 : subd5_1 [-3, -2, 5] = true := by decide +kernel
theorem subd5_1_65 : subd5_1 [-3, -2, 6] = true := by decide +kernel
theorem subd5_1_66 : subd5_1 [-3, -2, 7] = true := by decide +kernel
theorem subd5_1_67 : subd5_1 [-3, -2, 8] = true := by decide +kernel
theorem subd5_1_68 : subd5_1 [-3, -1, -7] = true := by decide +kernel
theorem subd5_1_69 : subd5_1 [-3, -1, -6] = true := by decide +kernel
theorem subd5_1_70 : subd5_1 [-3, -1, -5] = true := by decide +kernel
theorem subd5_1_71 : subd5_1 [-3, -1, -4] = true := by decide +kernel
theorem subd5_1_72 : subd5_1 [-3, -1, -3] = true := by decide +kernel
theorem subd5_1_73 : subd5_1 [-3, -1, -2] = true := by decide +kernel
theorem subd5_1_74 : subd5_1 [-3, -1, -1] = true := by decide +kernel
theorem subd5_1_75 : subd5_1 [-3, -1, 0] = true := by decide +kernel
theorem subd5_1_76 : subd5_1 [-3, -1, 1] = true := by decide +kernel
theorem subd5_1_77 : subd5_1 [-3, -1, 2] = true := by decide +kernel
theorem subd5_1_78 : subd5_1 [-3, -1, 3] = true := by decide +kernel
theorem subd5_1_79 : subd5_1 [-3, -1, 4] = true := by decide +kernel
theorem subd5_1_80 : subd5_1 [-3, -1, 5] = true := by decide +kernel
theorem subd5_1_81 : subd5_1 [-3, -1, 6] = true := by decide +kernel
theorem subd5_1_82 : subd5_1 [-3, -1, 7] = true := by decide +kernel
theorem subd5_1_83 : subd5_1 [-3, -1, 8] = true := by decide +kernel
theorem subd5_1_84 : subd5_1 [-3, 0, -7] = true := by decide +kernel
theorem subd5_1_85 : subd5_1 [-3, 0, -6] = true := by decide +kernel
theorem subd5_1_86 : subd5_1 [-3, 0, -5] = true := by decide +kernel
theorem subd5_1_87 : subd5_1 [-3, 0, -4] = true := by decide +kernel
theorem subd5_1_88 : subd5_1 [-3, 0, -3] = true := by decide +kernel
theorem subd5_1_89 : subd5_1 [-3, 0, -2] = true := by decide +kernel
theorem subd5_1_90 : subd5_1 [-3, 0, -1] = true := by decide +kernel
theorem subd5_1_91 : subd5_1 [-3, 0, 0] = true := by decide +kernel
theorem subd5_1_92 : subd5_1 [-3, 0, 1] = true := by decide +kernel
theorem subd5_1_93 : subd5_1 [-3, 0, 2] = true := by decide +kernel
theorem subd5_1_94 : subd5_1 [-3, 0, 3] = true := by decide +kernel
theorem subd5_1_95 : subd5_1 [-3, 0, 4] = true := by decide +kernel
theorem sbd5_1_2 : ∀ q ∈ blkd5_1_2, subd5_1 q = true := by
  unfold blkd5_1_2
  exact List.forall_mem_cons.2 ⟨subd5_1_64, List.forall_mem_cons.2 ⟨subd5_1_65, List.forall_mem_cons.2 ⟨subd5_1_66, List.forall_mem_cons.2 ⟨subd5_1_67, List.forall_mem_cons.2 ⟨subd5_1_68, List.forall_mem_cons.2 ⟨subd5_1_69, List.forall_mem_cons.2 ⟨subd5_1_70, List.forall_mem_cons.2 ⟨subd5_1_71, List.forall_mem_cons.2 ⟨subd5_1_72, List.forall_mem_cons.2 ⟨subd5_1_73, List.forall_mem_cons.2 ⟨subd5_1_74, List.forall_mem_cons.2 ⟨subd5_1_75, List.forall_mem_cons.2 ⟨subd5_1_76, List.forall_mem_cons.2 ⟨subd5_1_77, List.forall_mem_cons.2 ⟨subd5_1_78, List.forall_mem_cons.2 ⟨subd5_1_79, List.forall_mem_cons.2 ⟨subd5_1_80, List.forall_mem_cons.2 ⟨subd5_1_81, List.forall_mem_cons.2 ⟨subd5_1_82, List.forall_mem_cons.2 ⟨subd5_1_83, List.forall_mem_cons.2 ⟨subd5_1_84, List.forall_mem_cons.2 ⟨subd5_1_85, List.forall_mem_cons.2 ⟨subd5_1_86, List.forall_mem_cons.2 ⟨subd5_1_87, List.forall_mem_cons.2 ⟨subd5_1_88, List.forall_mem_cons.2 ⟨subd5_1_89, List.forall_mem_cons.2 ⟨subd5_1_90, List.forall_mem_cons.2 ⟨subd5_1_91, List.forall_mem_cons.2 ⟨subd5_1_92, List.forall_mem_cons.2 ⟨subd5_1_93, List.forall_mem_cons.2 ⟨subd5_1_94, List.forall_mem_cons.2 ⟨subd5_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
