import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-8] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-7, -5] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [-7, -4] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [-7, -3] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [-7, -2] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [-7, -1] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [-7, 0] = true := by decide +kernel
theorem subd9_5_7 : subd9_5 [-7, 1] = true := by decide +kernel
theorem subd9_5_8 : subd9_5 [-7, 2] = true := by decide +kernel
theorem subd9_5_9 : subd9_5 [-6, -6] = true := by decide +kernel
theorem subd9_5_10 : subd9_5 [-6, -5] = true := by decide +kernel
theorem subd9_5_11 : subd9_5 [-6, -4] = true := by decide +kernel
theorem subd9_5_12 : subd9_5 [-6, -3] = true := by decide +kernel
theorem subd9_5_13 : subd9_5 [-6, -2] = true := by decide +kernel
theorem subd9_5_14 : subd9_5 [-6, -1] = true := by decide +kernel
theorem subd9_5_15 : subd9_5 [-6, 0] = true := by decide +kernel
theorem subd9_5_16 : subd9_5 [-6, 1] = true := by decide +kernel
theorem subd9_5_17 : subd9_5 [-6, 2] = true := by decide +kernel
theorem subd9_5_18 : subd9_5 [-6, 3] = true := by decide +kernel
theorem subd9_5_19 : subd9_5 [-5, -7] = true := by decide +kernel
theorem subd9_5_20 : subd9_5 [-5, -6] = true := by decide +kernel
theorem subd9_5_21 : subd9_5 [-5, -5] = true := by decide +kernel
theorem subd9_5_22 : subd9_5 [-5, -4] = true := by decide +kernel
theorem subd9_5_23 : subd9_5 [-5, -3] = true := by decide +kernel
theorem subd9_5_24 : subd9_5 [-5, -2] = true := by decide +kernel
theorem subd9_5_25 : subd9_5 [-5, -1] = true := by decide +kernel
theorem subd9_5_26 : subd9_5 [-5, 0] = true := by decide +kernel
theorem subd9_5_27 : subd9_5 [-5, 1] = true := by decide +kernel
theorem subd9_5_28 : subd9_5 [-5, 2] = true := by decide +kernel
theorem subd9_5_29 : subd9_5 [-5, 3] = true := by decide +kernel
theorem subd9_5_30 : subd9_5 [-5, 4] = true := by decide +kernel
theorem subd9_5_31 : subd9_5 [-4, -7] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_cons.2 ⟨subd9_5_7, List.forall_mem_cons.2 ⟨subd9_5_8, List.forall_mem_cons.2 ⟨subd9_5_9, List.forall_mem_cons.2 ⟨subd9_5_10, List.forall_mem_cons.2 ⟨subd9_5_11, List.forall_mem_cons.2 ⟨subd9_5_12, List.forall_mem_cons.2 ⟨subd9_5_13, List.forall_mem_cons.2 ⟨subd9_5_14, List.forall_mem_cons.2 ⟨subd9_5_15, List.forall_mem_cons.2 ⟨subd9_5_16, List.forall_mem_cons.2 ⟨subd9_5_17, List.forall_mem_cons.2 ⟨subd9_5_18, List.forall_mem_cons.2 ⟨subd9_5_19, List.forall_mem_cons.2 ⟨subd9_5_20, List.forall_mem_cons.2 ⟨subd9_5_21, List.forall_mem_cons.2 ⟨subd9_5_22, List.forall_mem_cons.2 ⟨subd9_5_23, List.forall_mem_cons.2 ⟨subd9_5_24, List.forall_mem_cons.2 ⟨subd9_5_25, List.forall_mem_cons.2 ⟨subd9_5_26, List.forall_mem_cons.2 ⟨subd9_5_27, List.forall_mem_cons.2 ⟨subd9_5_28, List.forall_mem_cons.2 ⟨subd9_5_29, List.forall_mem_cons.2 ⟨subd9_5_30, List.forall_mem_cons.2 ⟨subd9_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_32 : subd9_5 [-4, -6] = true := by decide +kernel
theorem subd9_5_33 : subd9_5 [-4, -5] = true := by decide +kernel
theorem subd9_5_34 : subd9_5 [-4, -4] = true := by decide +kernel
theorem subd9_5_35 : subd9_5 [-4, -3] = true := by decide +kernel
theorem subd9_5_36 : subd9_5 [-4, -2] = true := by decide +kernel
theorem subd9_5_37 : subd9_5 [-4, -1] = true := by decide +kernel
theorem subd9_5_38 : subd9_5 [-4, 0] = true := by decide +kernel
theorem subd9_5_39 : subd9_5 [-4, 1] = true := by decide +kernel
theorem subd9_5_40 : subd9_5 [-4, 2] = true := by decide +kernel
theorem subd9_5_41 : subd9_5 [-4, 3] = true := by decide +kernel
theorem subd9_5_42 : subd9_5 [-4, 4] = true := by decide +kernel
theorem subd9_5_43 : subd9_5 [-4, 5] = true := by decide +kernel
theorem subd9_5_44 : subd9_5 [-3, -8] = true := by decide +kernel
theorem subd9_5_45 : subd9_5 [-3, -7] = true := by decide +kernel
theorem subd9_5_46 : subd9_5 [-3, -6] = true := by decide +kernel
theorem subd9_5_47 : subd9_5 [-3, -5] = true := by decide +kernel
theorem subd9_5_48 : subd9_5 [-3, -4] = true := by decide +kernel
theorem subd9_5_49 : subd9_5 [-3, -3] = true := by decide +kernel
theorem subd9_5_50 : subd9_5 [-3, -2] = true := by decide +kernel
theorem subd9_5_51 : subd9_5 [-3, -1] = true := by decide +kernel
theorem subd9_5_52 : subd9_5 [-3, 0] = true := by decide +kernel
theorem subd9_5_53 : subd9_5 [-3, 1] = true := by decide +kernel
theorem subd9_5_54 : subd9_5 [-3, 2] = true := by decide +kernel
theorem subd9_5_55 : subd9_5 [-3, 3] = true := by decide +kernel
theorem subd9_5_56 : subd9_5 [-3, 4] = true := by decide +kernel
theorem subd9_5_57 : subd9_5 [-3, 5] = true := by decide +kernel
theorem subd9_5_58 : subd9_5 [-3, 6] = true := by decide +kernel
theorem subd9_5_59 : subd9_5 [-2, -8] = true := by decide +kernel
theorem subd9_5_60 : subd9_5 [-2, -7] = true := by decide +kernel
theorem subd9_5_61 : subd9_5 [-2, -6] = true := by decide +kernel
theorem subd9_5_62 : subd9_5 [-2, -5] = true := by decide +kernel
theorem subd9_5_63 : subd9_5 [-2, -4] = true := by decide +kernel
theorem sbd9_5_1 : ∀ q ∈ blkd9_5_1, subd9_5 q = true := by
  unfold blkd9_5_1
  exact List.forall_mem_cons.2 ⟨subd9_5_32, List.forall_mem_cons.2 ⟨subd9_5_33, List.forall_mem_cons.2 ⟨subd9_5_34, List.forall_mem_cons.2 ⟨subd9_5_35, List.forall_mem_cons.2 ⟨subd9_5_36, List.forall_mem_cons.2 ⟨subd9_5_37, List.forall_mem_cons.2 ⟨subd9_5_38, List.forall_mem_cons.2 ⟨subd9_5_39, List.forall_mem_cons.2 ⟨subd9_5_40, List.forall_mem_cons.2 ⟨subd9_5_41, List.forall_mem_cons.2 ⟨subd9_5_42, List.forall_mem_cons.2 ⟨subd9_5_43, List.forall_mem_cons.2 ⟨subd9_5_44, List.forall_mem_cons.2 ⟨subd9_5_45, List.forall_mem_cons.2 ⟨subd9_5_46, List.forall_mem_cons.2 ⟨subd9_5_47, List.forall_mem_cons.2 ⟨subd9_5_48, List.forall_mem_cons.2 ⟨subd9_5_49, List.forall_mem_cons.2 ⟨subd9_5_50, List.forall_mem_cons.2 ⟨subd9_5_51, List.forall_mem_cons.2 ⟨subd9_5_52, List.forall_mem_cons.2 ⟨subd9_5_53, List.forall_mem_cons.2 ⟨subd9_5_54, List.forall_mem_cons.2 ⟨subd9_5_55, List.forall_mem_cons.2 ⟨subd9_5_56, List.forall_mem_cons.2 ⟨subd9_5_57, List.forall_mem_cons.2 ⟨subd9_5_58, List.forall_mem_cons.2 ⟨subd9_5_59, List.forall_mem_cons.2 ⟨subd9_5_60, List.forall_mem_cons.2 ⟨subd9_5_61, List.forall_mem_cons.2 ⟨subd9_5_62, List.forall_mem_cons.2 ⟨subd9_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_64 : subd9_5 [-2, -3] = true := by decide +kernel
theorem subd9_5_65 : subd9_5 [-2, -2] = true := by decide +kernel
theorem subd9_5_66 : subd9_5 [-2, -1] = true := by decide +kernel
theorem subd9_5_67 : subd9_5 [-2, 0] = true := by decide +kernel
theorem subd9_5_68 : subd9_5 [-2, 1] = true := by decide +kernel
theorem subd9_5_69 : subd9_5 [-2, 2] = true := by decide +kernel
theorem subd9_5_70 : subd9_5 [-2, 3] = true := by decide +kernel
theorem subd9_5_71 : subd9_5 [-2, 4] = true := by decide +kernel
theorem subd9_5_72 : subd9_5 [-2, 5] = true := by decide +kernel
theorem subd9_5_73 : subd9_5 [-2, 6] = true := by decide +kernel
theorem subd9_5_74 : subd9_5 [-1, -8] = true := by decide +kernel
theorem subd9_5_75 : subd9_5 [-1, -7] = true := by decide +kernel
theorem subd9_5_76 : subd9_5 [-1, -6] = true := by decide +kernel
theorem subd9_5_77 : subd9_5 [-1, -5] = true := by decide +kernel
theorem subd9_5_78 : subd9_5 [-1, -4] = true := by decide +kernel
theorem subd9_5_79 : subd9_5 [-1, -3] = true := by decide +kernel
theorem subd9_5_80 : subd9_5 [-1, -2] = true := by decide +kernel
theorem subd9_5_81 : subd9_5 [-1, -1] = true := by decide +kernel
theorem subd9_5_82 : subd9_5 [-1, 0] = true := by decide +kernel
theorem subd9_5_83 : subd9_5 [-1, 1] = true := by decide +kernel
theorem subd9_5_84 : subd9_5 [-1, 2] = true := by decide +kernel
theorem subd9_5_85 : subd9_5 [-1, 3] = true := by decide +kernel
theorem subd9_5_86 : subd9_5 [-1, 4] = true := by decide +kernel
theorem subd9_5_87 : subd9_5 [-1, 5] = true := by decide +kernel
theorem subd9_5_88 : subd9_5 [-1, 6] = true := by decide +kernel
theorem subd9_5_89 : subd9_5 [0, -8] = true := by decide +kernel
theorem subd9_5_90 : subd9_5 [0, -7] = true := by decide +kernel
theorem subd9_5_91 : subd9_5 [0, -6] = true := by decide +kernel
theorem subd9_5_92 : subd9_5 [0, -5] = true := by decide +kernel
theorem subd9_5_93 : subd9_5 [0, -4] = true := by decide +kernel
theorem subd9_5_94 : subd9_5 [0, -3] = true := by decide +kernel
theorem subd9_5_95 : subd9_5 [0, -2] = true := by decide +kernel
theorem sbd9_5_2 : ∀ q ∈ blkd9_5_2, subd9_5 q = true := by
  unfold blkd9_5_2
  exact List.forall_mem_cons.2 ⟨subd9_5_64, List.forall_mem_cons.2 ⟨subd9_5_65, List.forall_mem_cons.2 ⟨subd9_5_66, List.forall_mem_cons.2 ⟨subd9_5_67, List.forall_mem_cons.2 ⟨subd9_5_68, List.forall_mem_cons.2 ⟨subd9_5_69, List.forall_mem_cons.2 ⟨subd9_5_70, List.forall_mem_cons.2 ⟨subd9_5_71, List.forall_mem_cons.2 ⟨subd9_5_72, List.forall_mem_cons.2 ⟨subd9_5_73, List.forall_mem_cons.2 ⟨subd9_5_74, List.forall_mem_cons.2 ⟨subd9_5_75, List.forall_mem_cons.2 ⟨subd9_5_76, List.forall_mem_cons.2 ⟨subd9_5_77, List.forall_mem_cons.2 ⟨subd9_5_78, List.forall_mem_cons.2 ⟨subd9_5_79, List.forall_mem_cons.2 ⟨subd9_5_80, List.forall_mem_cons.2 ⟨subd9_5_81, List.forall_mem_cons.2 ⟨subd9_5_82, List.forall_mem_cons.2 ⟨subd9_5_83, List.forall_mem_cons.2 ⟨subd9_5_84, List.forall_mem_cons.2 ⟨subd9_5_85, List.forall_mem_cons.2 ⟨subd9_5_86, List.forall_mem_cons.2 ⟨subd9_5_87, List.forall_mem_cons.2 ⟨subd9_5_88, List.forall_mem_cons.2 ⟨subd9_5_89, List.forall_mem_cons.2 ⟨subd9_5_90, List.forall_mem_cons.2 ⟨subd9_5_91, List.forall_mem_cons.2 ⟨subd9_5_92, List.forall_mem_cons.2 ⟨subd9_5_93, List.forall_mem_cons.2 ⟨subd9_5_94, List.forall_mem_cons.2 ⟨subd9_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
