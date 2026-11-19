import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-5] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-4, -5] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-4, -4] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-4, -3] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-4, -2] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-4, -1] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-4, 0] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-4, 1] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [-4, 2] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [-3, -5] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [-3, -4] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [-3, -3] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [-3, -2] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [-3, -1] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [-3, 0] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [-3, 1] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [-3, 2] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [-3, 3] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [-2, -5] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [-2, -4] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [-2, -3] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [-2, -2] = true := by decide +kernel
theorem subd7_4_22 : subd7_4 [-2, -1] = true := by decide +kernel
theorem subd7_4_23 : subd7_4 [-2, 0] = true := by decide +kernel
theorem subd7_4_24 : subd7_4 [-2, 1] = true := by decide +kernel
theorem subd7_4_25 : subd7_4 [-2, 2] = true := by decide +kernel
theorem subd7_4_26 : subd7_4 [-2, 3] = true := by decide +kernel
theorem subd7_4_27 : subd7_4 [-1, -5] = true := by decide +kernel
theorem subd7_4_28 : subd7_4 [-1, -4] = true := by decide +kernel
theorem subd7_4_29 : subd7_4 [-1, -3] = true := by decide +kernel
theorem subd7_4_30 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_31 : subd7_4 [-1, -1] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_cons.2 ⟨subd7_4_22, List.forall_mem_cons.2 ⟨subd7_4_23, List.forall_mem_cons.2 ⟨subd7_4_24, List.forall_mem_cons.2 ⟨subd7_4_25, List.forall_mem_cons.2 ⟨subd7_4_26, List.forall_mem_cons.2 ⟨subd7_4_27, List.forall_mem_cons.2 ⟨subd7_4_28, List.forall_mem_cons.2 ⟨subd7_4_29, List.forall_mem_cons.2 ⟨subd7_4_30, List.forall_mem_cons.2 ⟨subd7_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_32 : subd7_4 [-1, 0] = true := by decide +kernel
theorem subd7_4_33 : subd7_4 [-1, 1] = true := by decide +kernel
theorem subd7_4_34 : subd7_4 [-1, 2] = true := by decide +kernel
theorem subd7_4_35 : subd7_4 [-1, 3] = true := by decide +kernel
theorem subd7_4_36 : subd7_4 [-1, 4] = true := by decide +kernel
theorem subd7_4_37 : subd7_4 [0, -5] = true := by decide +kernel
theorem subd7_4_38 : subd7_4 [0, -4] = true := by decide +kernel
theorem subd7_4_39 : subd7_4 [0, -3] = true := by decide +kernel
theorem subd7_4_40 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_41 : subd7_4 [0, -1] = true := by decide +kernel
theorem subd7_4_42 : subd7_4 [0, 0] = true := by decide +kernel
theorem subd7_4_43 : subd7_4 [0, 1] = true := by decide +kernel
theorem subd7_4_44 : subd7_4 [0, 2] = true := by decide +kernel
theorem subd7_4_45 : subd7_4 [0, 3] = true := by decide +kernel
theorem subd7_4_46 : subd7_4 [0, 4] = true := by decide +kernel
theorem subd7_4_47 : subd7_4 [1, -5] = true := by decide +kernel
theorem subd7_4_48 : subd7_4 [1, -4] = true := by decide +kernel
theorem subd7_4_49 : subd7_4 [1, -3] = true := by decide +kernel
theorem subd7_4_50 : subd7_4 [1, -2] = true := by decide +kernel
theorem subd7_4_51 : subd7_4 [1, -1] = true := by decide +kernel
theorem subd7_4_52 : subd7_4 [1, 0] = true := by decide +kernel
theorem subd7_4_53 : subd7_4 [1, 1] = true := by decide +kernel
theorem subd7_4_54 : subd7_4 [1, 2] = true := by decide +kernel
theorem subd7_4_55 : subd7_4 [1, 3] = true := by decide +kernel
theorem subd7_4_56 : subd7_4 [1, 4] = true := by decide +kernel
theorem subd7_4_57 : subd7_4 [2, -4] = true := by decide +kernel
theorem subd7_4_58 : subd7_4 [2, -3] = true := by decide +kernel
theorem subd7_4_59 : subd7_4 [2, -2] = true := by decide +kernel
theorem subd7_4_60 : subd7_4 [2, -1] = true := by decide +kernel
theorem subd7_4_61 : subd7_4 [2, 0] = true := by decide +kernel
theorem subd7_4_62 : subd7_4 [2, 1] = true := by decide +kernel
theorem subd7_4_63 : subd7_4 [2, 2] = true := by decide +kernel
theorem sbd7_4_1 : ∀ q ∈ blkd7_4_1, subd7_4 q = true := by
  unfold blkd7_4_1
  exact List.forall_mem_cons.2 ⟨subd7_4_32, List.forall_mem_cons.2 ⟨subd7_4_33, List.forall_mem_cons.2 ⟨subd7_4_34, List.forall_mem_cons.2 ⟨subd7_4_35, List.forall_mem_cons.2 ⟨subd7_4_36, List.forall_mem_cons.2 ⟨subd7_4_37, List.forall_mem_cons.2 ⟨subd7_4_38, List.forall_mem_cons.2 ⟨subd7_4_39, List.forall_mem_cons.2 ⟨subd7_4_40, List.forall_mem_cons.2 ⟨subd7_4_41, List.forall_mem_cons.2 ⟨subd7_4_42, List.forall_mem_cons.2 ⟨subd7_4_43, List.forall_mem_cons.2 ⟨subd7_4_44, List.forall_mem_cons.2 ⟨subd7_4_45, List.forall_mem_cons.2 ⟨subd7_4_46, List.forall_mem_cons.2 ⟨subd7_4_47, List.forall_mem_cons.2 ⟨subd7_4_48, List.forall_mem_cons.2 ⟨subd7_4_49, List.forall_mem_cons.2 ⟨subd7_4_50, List.forall_mem_cons.2 ⟨subd7_4_51, List.forall_mem_cons.2 ⟨subd7_4_52, List.forall_mem_cons.2 ⟨subd7_4_53, List.forall_mem_cons.2 ⟨subd7_4_54, List.forall_mem_cons.2 ⟨subd7_4_55, List.forall_mem_cons.2 ⟨subd7_4_56, List.forall_mem_cons.2 ⟨subd7_4_57, List.forall_mem_cons.2 ⟨subd7_4_58, List.forall_mem_cons.2 ⟨subd7_4_59, List.forall_mem_cons.2 ⟨subd7_4_60, List.forall_mem_cons.2 ⟨subd7_4_61, List.forall_mem_cons.2 ⟨subd7_4_62, List.forall_mem_cons.2 ⟨subd7_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_64 : subd7_4 [2, 3] = true := by decide +kernel
theorem subd7_4_65 : subd7_4 [2, 4] = true := by decide +kernel
theorem subd7_4_66 : subd7_4 [3, -4] = true := by decide +kernel
theorem subd7_4_67 : subd7_4 [3, -3] = true := by decide +kernel
theorem subd7_4_68 : subd7_4 [3, -2] = true := by decide +kernel
theorem subd7_4_69 : subd7_4 [3, -1] = true := by decide +kernel
theorem subd7_4_70 : subd7_4 [3, 0] = true := by decide +kernel
theorem subd7_4_71 : subd7_4 [3, 1] = true := by decide +kernel
theorem subd7_4_72 : subd7_4 [3, 2] = true := by decide +kernel
theorem subd7_4_73 : subd7_4 [3, 3] = true := by decide +kernel
theorem subd7_4_74 : subd7_4 [3, 4] = true := by decide +kernel
theorem subd7_4_75 : subd7_4 [4, -3] = true := by decide +kernel
theorem subd7_4_76 : subd7_4 [4, -2] = true := by decide +kernel
theorem subd7_4_77 : subd7_4 [4, -1] = true := by decide +kernel
theorem subd7_4_78 : subd7_4 [4, 0] = true := by decide +kernel
theorem subd7_4_79 : subd7_4 [4, 1] = true := by decide +kernel
theorem subd7_4_80 : subd7_4 [4, 2] = true := by decide +kernel
theorem subd7_4_81 : subd7_4 [4, 3] = true := by decide +kernel
theorem subd7_4_82 : subd7_4 [4, 4] = true := by decide +kernel
theorem subd7_4_83 : subd7_4 [5] = true := by decide +kernel
theorem sbd7_4_2 : ∀ q ∈ blkd7_4_2, subd7_4 q = true := by
  unfold blkd7_4_2
  exact List.forall_mem_cons.2 ⟨subd7_4_64, List.forall_mem_cons.2 ⟨subd7_4_65, List.forall_mem_cons.2 ⟨subd7_4_66, List.forall_mem_cons.2 ⟨subd7_4_67, List.forall_mem_cons.2 ⟨subd7_4_68, List.forall_mem_cons.2 ⟨subd7_4_69, List.forall_mem_cons.2 ⟨subd7_4_70, List.forall_mem_cons.2 ⟨subd7_4_71, List.forall_mem_cons.2 ⟨subd7_4_72, List.forall_mem_cons.2 ⟨subd7_4_73, List.forall_mem_cons.2 ⟨subd7_4_74, List.forall_mem_cons.2 ⟨subd7_4_75, List.forall_mem_cons.2 ⟨subd7_4_76, List.forall_mem_cons.2 ⟨subd7_4_77, List.forall_mem_cons.2 ⟨subd7_4_78, List.forall_mem_cons.2 ⟨subd7_4_79, List.forall_mem_cons.2 ⟨subd7_4_80, List.forall_mem_cons.2 ⟨subd7_4_81, List.forall_mem_cons.2 ⟨subd7_4_82, List.forall_mem_cons.2 ⟨subd7_4_83, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
