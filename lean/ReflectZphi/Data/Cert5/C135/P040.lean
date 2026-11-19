import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_6_32 : subd8_6 [-1, 0] = true := by decide +kernel
theorem subd8_6_33 : subd8_6 [-1, 1] = true := by decide +kernel
theorem subd8_6_34 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_35 : subd8_6 [-1, 3] = true := by decide +kernel
theorem subd8_6_36 : subd8_6 [-1, 4] = true := by decide +kernel
theorem subd8_6_37 : subd8_6 [0, -5] = true := by decide +kernel
theorem subd8_6_38 : subd8_6 [0, -4] = true := by decide +kernel
theorem subd8_6_39 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_40 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_41 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_42 : subd8_6 [0, 0] = true := by decide +kernel
theorem subd8_6_43 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_44 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_45 : subd8_6 [0, 3] = true := by decide +kernel
theorem subd8_6_46 : subd8_6 [0, 4] = true := by decide +kernel
theorem subd8_6_47 : subd8_6 [1, -5] = true := by decide +kernel
theorem subd8_6_48 : subd8_6 [1, -4] = true := by decide +kernel
theorem subd8_6_49 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_50 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_51 : subd8_6 [1, -1] = true := by decide +kernel
theorem subd8_6_52 : subd8_6 [1, 0] = true := by decide +kernel
theorem subd8_6_53 : subd8_6 [1, 1] = true := by decide +kernel
theorem subd8_6_54 : subd8_6 [1, 2] = true := by decide +kernel
theorem subd8_6_55 : subd8_6 [1, 3] = true := by decide +kernel
theorem subd8_6_56 : subd8_6 [1, 4] = true := by decide +kernel
theorem subd8_6_57 : subd8_6 [2, -5] = true := by decide +kernel
theorem subd8_6_58 : subd8_6 [2, -4] = true := by decide +kernel
theorem subd8_6_59 : subd8_6 [2, -3] = true := by decide +kernel
theorem subd8_6_60 : subd8_6 [2, -2] = true := by decide +kernel
theorem subd8_6_61 : subd8_6 [2, -1] = true := by decide +kernel
theorem subd8_6_62 : subd8_6 [2, 0] = true := by decide +kernel
theorem subd8_6_63 : subd8_6 [2, 1] = true := by decide +kernel
theorem sbd8_6_1 : ∀ q ∈ blkd8_6_1, subd8_6 q = true := by
  unfold blkd8_6_1
  exact List.forall_mem_cons.2 ⟨subd8_6_32, List.forall_mem_cons.2 ⟨subd8_6_33, List.forall_mem_cons.2 ⟨subd8_6_34, List.forall_mem_cons.2 ⟨subd8_6_35, List.forall_mem_cons.2 ⟨subd8_6_36, List.forall_mem_cons.2 ⟨subd8_6_37, List.forall_mem_cons.2 ⟨subd8_6_38, List.forall_mem_cons.2 ⟨subd8_6_39, List.forall_mem_cons.2 ⟨subd8_6_40, List.forall_mem_cons.2 ⟨subd8_6_41, List.forall_mem_cons.2 ⟨subd8_6_42, List.forall_mem_cons.2 ⟨subd8_6_43, List.forall_mem_cons.2 ⟨subd8_6_44, List.forall_mem_cons.2 ⟨subd8_6_45, List.forall_mem_cons.2 ⟨subd8_6_46, List.forall_mem_cons.2 ⟨subd8_6_47, List.forall_mem_cons.2 ⟨subd8_6_48, List.forall_mem_cons.2 ⟨subd8_6_49, List.forall_mem_cons.2 ⟨subd8_6_50, List.forall_mem_cons.2 ⟨subd8_6_51, List.forall_mem_cons.2 ⟨subd8_6_52, List.forall_mem_cons.2 ⟨subd8_6_53, List.forall_mem_cons.2 ⟨subd8_6_54, List.forall_mem_cons.2 ⟨subd8_6_55, List.forall_mem_cons.2 ⟨subd8_6_56, List.forall_mem_cons.2 ⟨subd8_6_57, List.forall_mem_cons.2 ⟨subd8_6_58, List.forall_mem_cons.2 ⟨subd8_6_59, List.forall_mem_cons.2 ⟨subd8_6_60, List.forall_mem_cons.2 ⟨subd8_6_61, List.forall_mem_cons.2 ⟨subd8_6_62, List.forall_mem_cons.2 ⟨subd8_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_6_64 : subd8_6 [2, 2] = true := by decide +kernel
theorem subd8_6_65 : subd8_6 [2, 3] = true := by decide +kernel
theorem subd8_6_66 : subd8_6 [2, 4] = true := by decide +kernel
theorem subd8_6_67 : subd8_6 [3, -5] = true := by decide +kernel
theorem subd8_6_68 : subd8_6 [3, -4] = true := by decide +kernel
theorem subd8_6_69 : subd8_6 [3, -3] = true := by decide +kernel
theorem subd8_6_70 : subd8_6 [3, -2] = true := by decide +kernel
theorem subd8_6_71 : subd8_6 [3, -1] = true := by decide +kernel
theorem subd8_6_72 : subd8_6 [3, 0] = true := by decide +kernel
theorem subd8_6_73 : subd8_6 [3, 1] = true := by decide +kernel
theorem subd8_6_74 : subd8_6 [3, 2] = true := by decide +kernel
theorem subd8_6_75 : subd8_6 [3, 3] = true := by decide +kernel
theorem subd8_6_76 : subd8_6 [4, -4] = true := by decide +kernel
theorem subd8_6_77 : subd8_6 [4, -3] = true := by decide +kernel
theorem subd8_6_78 : subd8_6 [4, -2] = true := by decide +kernel
theorem subd8_6_79 : subd8_6 [4, -1] = true := by decide +kernel
theorem subd8_6_80 : subd8_6 [4, 0] = true := by decide +kernel
theorem subd8_6_81 : subd8_6 [4, 1] = true := by decide +kernel
theorem subd8_6_82 : subd8_6 [4, 2] = true := by decide +kernel
theorem subd8_6_83 : subd8_6 [5] = true := by decide +kernel
theorem sbd8_6_2 : ∀ q ∈ blkd8_6_2, subd8_6 q = true := by
  unfold blkd8_6_2
  exact List.forall_mem_cons.2 ⟨subd8_6_64, List.forall_mem_cons.2 ⟨subd8_6_65, List.forall_mem_cons.2 ⟨subd8_6_66, List.forall_mem_cons.2 ⟨subd8_6_67, List.forall_mem_cons.2 ⟨subd8_6_68, List.forall_mem_cons.2 ⟨subd8_6_69, List.forall_mem_cons.2 ⟨subd8_6_70, List.forall_mem_cons.2 ⟨subd8_6_71, List.forall_mem_cons.2 ⟨subd8_6_72, List.forall_mem_cons.2 ⟨subd8_6_73, List.forall_mem_cons.2 ⟨subd8_6_74, List.forall_mem_cons.2 ⟨subd8_6_75, List.forall_mem_cons.2 ⟨subd8_6_76, List.forall_mem_cons.2 ⟨subd8_6_77, List.forall_mem_cons.2 ⟨subd8_6_78, List.forall_mem_cons.2 ⟨subd8_6_79, List.forall_mem_cons.2 ⟨subd8_6_80, List.forall_mem_cons.2 ⟨subd8_6_81, List.forall_mem_cons.2 ⟨subd8_6_82, List.forall_mem_cons.2 ⟨subd8_6_83, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [-5] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-4, -3] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [-4, -2] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [-4, -1] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [-4, 0] = true := by decide +kernel
theorem subd8_7_5 : subd8_7 [-4, 1] = true := by decide +kernel
theorem subd8_7_6 : subd8_7 [-4, 2] = true := by decide +kernel
theorem subd8_7_7 : subd8_7 [-4, 3] = true := by decide +kernel
theorem subd8_7_8 : subd8_7 [-4, 4] = true := by decide +kernel
theorem subd8_7_9 : subd8_7 [-3, -4] = true := by decide +kernel
theorem subd8_7_10 : subd8_7 [-3, -3] = true := by decide +kernel
theorem subd8_7_11 : subd8_7 [-3, -2] = true := by decide +kernel
theorem subd8_7_12 : subd8_7 [-3, -1] = true := by decide +kernel
theorem subd8_7_13 : subd8_7 [-3, 0] = true := by decide +kernel
theorem subd8_7_14 : subd8_7 [-3, 1] = true := by decide +kernel
theorem subd8_7_15 : subd8_7 [-3, 2] = true := by decide +kernel
theorem subd8_7_16 : subd8_7 [-3, 3] = true := by decide +kernel
theorem subd8_7_17 : subd8_7 [-3, 4] = true := by decide +kernel
theorem subd8_7_18 : subd8_7 [-3, 5] = true := by decide +kernel
theorem subd8_7_19 : subd8_7 [-2, -5] = true := by decide +kernel
theorem subd8_7_20 : subd8_7 [-2, -4] = true := by decide +kernel
theorem subd8_7_21 : subd8_7 [-2, -3] = true := by decide +kernel
theorem subd8_7_22 : subd8_7 [-2, -2] = true := by decide +kernel
theorem subd8_7_23 : subd8_7 [-2, -1] = true := by decide +kernel
theorem subd8_7_24 : subd8_7 [-2, 0] = true := by decide +kernel
theorem subd8_7_25 : subd8_7 [-2, 1] = true := by decide +kernel
theorem subd8_7_26 : subd8_7 [-2, 2] = true := by decide +kernel
theorem subd8_7_27 : subd8_7 [-2, 3] = true := by decide +kernel
theorem subd8_7_28 : subd8_7 [-2, 4] = true := by decide +kernel
theorem subd8_7_29 : subd8_7 [-2, 5] = true := by decide +kernel
theorem subd8_7_30 : subd8_7 [-1, -5] = true := by decide +kernel
theorem subd8_7_31 : subd8_7 [-1, -4] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_cons.2 ⟨subd8_7_5, List.forall_mem_cons.2 ⟨subd8_7_6, List.forall_mem_cons.2 ⟨subd8_7_7, List.forall_mem_cons.2 ⟨subd8_7_8, List.forall_mem_cons.2 ⟨subd8_7_9, List.forall_mem_cons.2 ⟨subd8_7_10, List.forall_mem_cons.2 ⟨subd8_7_11, List.forall_mem_cons.2 ⟨subd8_7_12, List.forall_mem_cons.2 ⟨subd8_7_13, List.forall_mem_cons.2 ⟨subd8_7_14, List.forall_mem_cons.2 ⟨subd8_7_15, List.forall_mem_cons.2 ⟨subd8_7_16, List.forall_mem_cons.2 ⟨subd8_7_17, List.forall_mem_cons.2 ⟨subd8_7_18, List.forall_mem_cons.2 ⟨subd8_7_19, List.forall_mem_cons.2 ⟨subd8_7_20, List.forall_mem_cons.2 ⟨subd8_7_21, List.forall_mem_cons.2 ⟨subd8_7_22, List.forall_mem_cons.2 ⟨subd8_7_23, List.forall_mem_cons.2 ⟨subd8_7_24, List.forall_mem_cons.2 ⟨subd8_7_25, List.forall_mem_cons.2 ⟨subd8_7_26, List.forall_mem_cons.2 ⟨subd8_7_27, List.forall_mem_cons.2 ⟨subd8_7_28, List.forall_mem_cons.2 ⟨subd8_7_29, List.forall_mem_cons.2 ⟨subd8_7_30, List.forall_mem_cons.2 ⟨subd8_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_7_32 : subd8_7 [-1, -3] = true := by decide +kernel
theorem subd8_7_33 : subd8_7 [-1, -2] = true := by decide +kernel
theorem subd8_7_34 : subd8_7 [-1, -1] = true := by decide +kernel
theorem subd8_7_35 : subd8_7 [-1, 0] = true := by decide +kernel
theorem subd8_7_36 : subd8_7 [-1, 1] = true := by decide +kernel
theorem subd8_7_37 : subd8_7 [-1, 2] = true := by decide +kernel
theorem subd8_7_38 : subd8_7 [-1, 3] = true := by decide +kernel
theorem subd8_7_39 : subd8_7 [-1, 4] = true := by decide +kernel
theorem subd8_7_40 : subd8_7 [-1, 5] = true := by decide +kernel
theorem subd8_7_41 : subd8_7 [0, -6] = true := by decide +kernel
theorem subd8_7_42 : subd8_7 [0, -5] = true := by decide +kernel
theorem subd8_7_43 : subd8_7 [0, -4] = true := by decide +kernel
theorem subd8_7_44 : subd8_7 [0, -3] = true := by decide +kernel
theorem subd8_7_45 : subd8_7 [0, -2] = true := by decide +kernel
theorem subd8_7_46 : subd8_7 [0, -1] = true := by decide +kernel
theorem subd8_7_47 : subd8_7 [0, 0] = true := by decide +kernel
theorem subd8_7_48 : subd8_7 [0, 1] = true := by decide +kernel
theorem subd8_7_49 : subd8_7 [0, 2] = true := by decide +kernel
theorem subd8_7_50 : subd8_7 [0, 3] = true := by decide +kernel
theorem subd8_7_51 : subd8_7 [0, 4] = true := by decide +kernel
theorem subd8_7_52 : subd8_7 [0, 5] = true := by decide +kernel
theorem subd8_7_53 : subd8_7 [1, -6] = true := by decide +kernel
theorem subd8_7_54 : subd8_7 [1, -5] = true := by decide +kernel
theorem subd8_7_55 : subd8_7 [1, -4] = true := by decide +kernel
theorem subd8_7_56 : subd8_7 [1, -3] = true := by decide +kernel
theorem subd8_7_57 : subd8_7 [1, -2] = true := by decide +kernel
theorem subd8_7_58 : subd8_7 [1, -1] = true := by decide +kernel
theorem subd8_7_59 : subd8_7 [1, 0] = true := by decide +kernel
theorem subd8_7_60 : subd8_7 [1, 1] = true := by decide +kernel
theorem subd8_7_61 : subd8_7 [1, 2] = true := by decide +kernel
theorem subd8_7_62 : subd8_7 [1, 3] = true := by decide +kernel
theorem subd8_7_63 : subd8_7 [1, 4] = true := by decide +kernel
theorem sbd8_7_1 : ∀ q ∈ blkd8_7_1, subd8_7 q = true := by
  unfold blkd8_7_1
  exact List.forall_mem_cons.2 ⟨subd8_7_32, List.forall_mem_cons.2 ⟨subd8_7_33, List.forall_mem_cons.2 ⟨subd8_7_34, List.forall_mem_cons.2 ⟨subd8_7_35, List.forall_mem_cons.2 ⟨subd8_7_36, List.forall_mem_cons.2 ⟨subd8_7_37, List.forall_mem_cons.2 ⟨subd8_7_38, List.forall_mem_cons.2 ⟨subd8_7_39, List.forall_mem_cons.2 ⟨subd8_7_40, List.forall_mem_cons.2 ⟨subd8_7_41, List.forall_mem_cons.2 ⟨subd8_7_42, List.forall_mem_cons.2 ⟨subd8_7_43, List.forall_mem_cons.2 ⟨subd8_7_44, List.forall_mem_cons.2 ⟨subd8_7_45, List.forall_mem_cons.2 ⟨subd8_7_46, List.forall_mem_cons.2 ⟨subd8_7_47, List.forall_mem_cons.2 ⟨subd8_7_48, List.forall_mem_cons.2 ⟨subd8_7_49, List.forall_mem_cons.2 ⟨subd8_7_50, List.forall_mem_cons.2 ⟨subd8_7_51, List.forall_mem_cons.2 ⟨subd8_7_52, List.forall_mem_cons.2 ⟨subd8_7_53, List.forall_mem_cons.2 ⟨subd8_7_54, List.forall_mem_cons.2 ⟨subd8_7_55, List.forall_mem_cons.2 ⟨subd8_7_56, List.forall_mem_cons.2 ⟨subd8_7_57, List.forall_mem_cons.2 ⟨subd8_7_58, List.forall_mem_cons.2 ⟨subd8_7_59, List.forall_mem_cons.2 ⟨subd8_7_60, List.forall_mem_cons.2 ⟨subd8_7_61, List.forall_mem_cons.2 ⟨subd8_7_62, List.forall_mem_cons.2 ⟨subd8_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
