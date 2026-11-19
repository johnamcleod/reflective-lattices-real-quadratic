import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd20_1_32 : subd20_1 [-1, 3] = true := by decide +kernel
theorem subd20_1_33 : subd20_1 [-1, 4] = true := by decide +kernel
theorem subd20_1_34 : subd20_1 [0, -5] = true := by decide +kernel
theorem subd20_1_35 : subd20_1 [0, -4] = true := by decide +kernel
theorem subd20_1_36 : subd20_1 [0, -3] = true := by decide +kernel
theorem subd20_1_37 : subd20_1 [0, -2] = true := by decide +kernel
theorem subd20_1_38 : subd20_1 [0, -1] = true := by decide +kernel
theorem subd20_1_39 : subd20_1 [0, 0] = true := by decide +kernel
theorem subd20_1_40 : subd20_1 [0, 1] = true := by decide +kernel
theorem subd20_1_41 : subd20_1 [0, 2] = true := by decide +kernel
theorem subd20_1_42 : subd20_1 [0, 3] = true := by decide +kernel
theorem subd20_1_43 : subd20_1 [0, 4] = true := by decide +kernel
theorem subd20_1_44 : subd20_1 [1, -5] = true := by decide +kernel
theorem subd20_1_45 : subd20_1 [1, -4] = true := by decide +kernel
theorem subd20_1_46 : subd20_1 [1, -3] = true := by decide +kernel
theorem subd20_1_47 : subd20_1 [1, -2] = true := by decide +kernel
theorem subd20_1_48 : subd20_1 [1, -1] = true := by decide +kernel
theorem subd20_1_49 : subd20_1 [1, 0] = true := by decide +kernel
theorem subd20_1_50 : subd20_1 [1, 1] = true := by decide +kernel
theorem subd20_1_51 : subd20_1 [1, 2] = true := by decide +kernel
theorem subd20_1_52 : subd20_1 [1, 3] = true := by decide +kernel
theorem subd20_1_53 : subd20_1 [1, 4] = true := by decide +kernel
theorem subd20_1_54 : subd20_1 [2, -5] = true := by decide +kernel
theorem subd20_1_55 : subd20_1 [2, -4] = true := by decide +kernel
theorem subd20_1_56 : subd20_1 [2, -3] = true := by decide +kernel
theorem subd20_1_57 : subd20_1 [2, -2] = true := by decide +kernel
theorem subd20_1_58 : subd20_1 [2, -1] = true := by decide +kernel
theorem subd20_1_59 : subd20_1 [2, 0] = true := by decide +kernel
theorem subd20_1_60 : subd20_1 [2, 1] = true := by decide +kernel
theorem subd20_1_61 : subd20_1 [2, 2] = true := by decide +kernel
theorem subd20_1_62 : subd20_1 [2, 3] = true := by decide +kernel
theorem subd20_1_63 : subd20_1 [2, 4] = true := by decide +kernel
theorem sbd20_1_1 : ∀ q ∈ blkd20_1_1, subd20_1 q = true := by
  unfold blkd20_1_1
  exact List.forall_mem_cons.2 ⟨subd20_1_32, List.forall_mem_cons.2 ⟨subd20_1_33, List.forall_mem_cons.2 ⟨subd20_1_34, List.forall_mem_cons.2 ⟨subd20_1_35, List.forall_mem_cons.2 ⟨subd20_1_36, List.forall_mem_cons.2 ⟨subd20_1_37, List.forall_mem_cons.2 ⟨subd20_1_38, List.forall_mem_cons.2 ⟨subd20_1_39, List.forall_mem_cons.2 ⟨subd20_1_40, List.forall_mem_cons.2 ⟨subd20_1_41, List.forall_mem_cons.2 ⟨subd20_1_42, List.forall_mem_cons.2 ⟨subd20_1_43, List.forall_mem_cons.2 ⟨subd20_1_44, List.forall_mem_cons.2 ⟨subd20_1_45, List.forall_mem_cons.2 ⟨subd20_1_46, List.forall_mem_cons.2 ⟨subd20_1_47, List.forall_mem_cons.2 ⟨subd20_1_48, List.forall_mem_cons.2 ⟨subd20_1_49, List.forall_mem_cons.2 ⟨subd20_1_50, List.forall_mem_cons.2 ⟨subd20_1_51, List.forall_mem_cons.2 ⟨subd20_1_52, List.forall_mem_cons.2 ⟨subd20_1_53, List.forall_mem_cons.2 ⟨subd20_1_54, List.forall_mem_cons.2 ⟨subd20_1_55, List.forall_mem_cons.2 ⟨subd20_1_56, List.forall_mem_cons.2 ⟨subd20_1_57, List.forall_mem_cons.2 ⟨subd20_1_58, List.forall_mem_cons.2 ⟨subd20_1_59, List.forall_mem_cons.2 ⟨subd20_1_60, List.forall_mem_cons.2 ⟨subd20_1_61, List.forall_mem_cons.2 ⟨subd20_1_62, List.forall_mem_cons.2 ⟨subd20_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_1_64 : subd20_1 [3, -4] = true := by decide +kernel
theorem subd20_1_65 : subd20_1 [3, -3] = true := by decide +kernel
theorem subd20_1_66 : subd20_1 [3, -2] = true := by decide +kernel
theorem subd20_1_67 : subd20_1 [3, -1] = true := by decide +kernel
theorem subd20_1_68 : subd20_1 [3, 0] = true := by decide +kernel
theorem subd20_1_69 : subd20_1 [3, 1] = true := by decide +kernel
theorem subd20_1_70 : subd20_1 [3, 2] = true := by decide +kernel
theorem subd20_1_71 : subd20_1 [3, 3] = true := by decide +kernel
theorem subd20_1_72 : subd20_1 [4, -3] = true := by decide +kernel
theorem subd20_1_73 : subd20_1 [4, -2] = true := by decide +kernel
theorem subd20_1_74 : subd20_1 [4, -1] = true := by decide +kernel
theorem subd20_1_75 : subd20_1 [4, 0] = true := by decide +kernel
theorem subd20_1_76 : subd20_1 [4, 1] = true := by decide +kernel
theorem subd20_1_77 : subd20_1 [4, 2] = true := by decide +kernel
theorem sbd20_1_2 : ∀ q ∈ blkd20_1_2, subd20_1 q = true := by
  unfold blkd20_1_2
  exact List.forall_mem_cons.2 ⟨subd20_1_64, List.forall_mem_cons.2 ⟨subd20_1_65, List.forall_mem_cons.2 ⟨subd20_1_66, List.forall_mem_cons.2 ⟨subd20_1_67, List.forall_mem_cons.2 ⟨subd20_1_68, List.forall_mem_cons.2 ⟨subd20_1_69, List.forall_mem_cons.2 ⟨subd20_1_70, List.forall_mem_cons.2 ⟨subd20_1_71, List.forall_mem_cons.2 ⟨subd20_1_72, List.forall_mem_cons.2 ⟨subd20_1_73, List.forall_mem_cons.2 ⟨subd20_1_74, List.forall_mem_cons.2 ⟨subd20_1_75, List.forall_mem_cons.2 ⟨subd20_1_76, List.forall_mem_cons.2 ⟨subd20_1_77, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd20_2 : ldCheck G d20_2.U d20_2.ms ldd20_2 = true := by decide +kernel
theorem pre_okd20_2 : subPre G cell20 d20_2 = true := by decide +kernel
theorem subd20_2_0 : subd20_2 [-4, -3] = true := by decide +kernel
theorem subd20_2_1 : subd20_2 [-4, -2] = true := by decide +kernel
theorem subd20_2_2 : subd20_2 [-4, -1] = true := by decide +kernel
theorem subd20_2_3 : subd20_2 [-4, 0] = true := by decide +kernel
theorem subd20_2_4 : subd20_2 [-4, 1] = true := by decide +kernel
theorem subd20_2_5 : subd20_2 [-4, 2] = true := by decide +kernel
theorem subd20_2_6 : subd20_2 [-4, 3] = true := by decide +kernel
theorem subd20_2_7 : subd20_2 [-4, 4] = true := by decide +kernel
theorem subd20_2_8 : subd20_2 [-3, -4] = true := by decide +kernel
theorem subd20_2_9 : subd20_2 [-3, -3] = true := by decide +kernel
theorem subd20_2_10 : subd20_2 [-3, -2] = true := by decide +kernel
theorem subd20_2_11 : subd20_2 [-3, -1] = true := by decide +kernel
theorem subd20_2_12 : subd20_2 [-3, 0] = true := by decide +kernel
theorem subd20_2_13 : subd20_2 [-3, 1] = true := by decide +kernel
theorem subd20_2_14 : subd20_2 [-3, 2] = true := by decide +kernel
theorem subd20_2_15 : subd20_2 [-3, 3] = true := by decide +kernel
theorem subd20_2_16 : subd20_2 [-3, 4] = true := by decide +kernel
theorem subd20_2_17 : subd20_2 [-3, 5] = true := by decide +kernel
theorem subd20_2_18 : subd20_2 [-2, -5] = true := by decide +kernel
theorem subd20_2_19 : subd20_2 [-2, -4] = true := by decide +kernel
theorem subd20_2_20 : subd20_2 [-2, -3] = true := by decide +kernel
theorem subd20_2_21 : subd20_2 [-2, -2] = true := by decide +kernel
theorem subd20_2_22 : subd20_2 [-2, -1] = true := by decide +kernel
theorem subd20_2_23 : subd20_2 [-2, 0] = true := by decide +kernel
theorem subd20_2_24 : subd20_2 [-2, 1] = true := by decide +kernel
theorem subd20_2_25 : subd20_2 [-2, 2] = true := by decide +kernel
theorem subd20_2_26 : subd20_2 [-2, 3] = true := by decide +kernel
theorem subd20_2_27 : subd20_2 [-2, 4] = true := by decide +kernel
theorem subd20_2_28 : subd20_2 [-2, 5] = true := by decide +kernel
theorem subd20_2_29 : subd20_2 [-1, -6] = true := by decide +kernel
theorem subd20_2_30 : subd20_2 [-1, -5] = true := by decide +kernel
theorem subd20_2_31 : subd20_2 [-1, -4] = true := by decide +kernel
theorem sbd20_2_0 : ∀ q ∈ blkd20_2_0, subd20_2 q = true := by
  unfold blkd20_2_0
  exact List.forall_mem_cons.2 ⟨subd20_2_0, List.forall_mem_cons.2 ⟨subd20_2_1, List.forall_mem_cons.2 ⟨subd20_2_2, List.forall_mem_cons.2 ⟨subd20_2_3, List.forall_mem_cons.2 ⟨subd20_2_4, List.forall_mem_cons.2 ⟨subd20_2_5, List.forall_mem_cons.2 ⟨subd20_2_6, List.forall_mem_cons.2 ⟨subd20_2_7, List.forall_mem_cons.2 ⟨subd20_2_8, List.forall_mem_cons.2 ⟨subd20_2_9, List.forall_mem_cons.2 ⟨subd20_2_10, List.forall_mem_cons.2 ⟨subd20_2_11, List.forall_mem_cons.2 ⟨subd20_2_12, List.forall_mem_cons.2 ⟨subd20_2_13, List.forall_mem_cons.2 ⟨subd20_2_14, List.forall_mem_cons.2 ⟨subd20_2_15, List.forall_mem_cons.2 ⟨subd20_2_16, List.forall_mem_cons.2 ⟨subd20_2_17, List.forall_mem_cons.2 ⟨subd20_2_18, List.forall_mem_cons.2 ⟨subd20_2_19, List.forall_mem_cons.2 ⟨subd20_2_20, List.forall_mem_cons.2 ⟨subd20_2_21, List.forall_mem_cons.2 ⟨subd20_2_22, List.forall_mem_cons.2 ⟨subd20_2_23, List.forall_mem_cons.2 ⟨subd20_2_24, List.forall_mem_cons.2 ⟨subd20_2_25, List.forall_mem_cons.2 ⟨subd20_2_26, List.forall_mem_cons.2 ⟨subd20_2_27, List.forall_mem_cons.2 ⟨subd20_2_28, List.forall_mem_cons.2 ⟨subd20_2_29, List.forall_mem_cons.2 ⟨subd20_2_30, List.forall_mem_cons.2 ⟨subd20_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd20_2_32 : subd20_2 [-1, -3] = true := by decide +kernel
theorem subd20_2_33 : subd20_2 [-1, -2] = true := by decide +kernel
theorem subd20_2_34 : subd20_2 [-1, -1] = true := by decide +kernel
theorem subd20_2_35 : subd20_2 [-1, 0] = true := by decide +kernel
theorem subd20_2_36 : subd20_2 [-1, 1] = true := by decide +kernel
theorem subd20_2_37 : subd20_2 [-1, 2] = true := by decide +kernel
theorem subd20_2_38 : subd20_2 [-1, 3] = true := by decide +kernel
theorem subd20_2_39 : subd20_2 [-1, 4] = true := by decide +kernel
theorem subd20_2_40 : subd20_2 [-1, 5] = true := by decide +kernel
theorem subd20_2_41 : subd20_2 [-1, 6] = true := by decide +kernel
theorem subd20_2_42 : subd20_2 [0, -6] = true := by decide +kernel
theorem subd20_2_43 : subd20_2 [0, -5] = true := by decide +kernel
theorem subd20_2_44 : subd20_2 [0, -4] = true := by decide +kernel
theorem subd20_2_45 : subd20_2 [0, -3] = true := by decide +kernel
theorem subd20_2_46 : subd20_2 [0, -2] = true := by decide +kernel
theorem subd20_2_47 : subd20_2 [0, -1] = true := by decide +kernel
theorem subd20_2_48 : subd20_2 [0, 0] = true := by decide +kernel
theorem subd20_2_49 : subd20_2 [0, 1] = true := by decide +kernel
theorem subd20_2_50 : subd20_2 [0, 2] = true := by decide +kernel
theorem subd20_2_51 : subd20_2 [0, 3] = true := by decide +kernel
theorem subd20_2_52 : subd20_2 [0, 4] = true := by decide +kernel
theorem subd20_2_53 : subd20_2 [0, 5] = true := by decide +kernel
theorem subd20_2_54 : subd20_2 [1, -7] = true := by decide +kernel
theorem subd20_2_55 : subd20_2 [1, -6] = true := by decide +kernel
theorem subd20_2_56 : subd20_2 [1, -5] = true := by decide +kernel
theorem subd20_2_57 : subd20_2 [1, -4] = true := by decide +kernel
theorem subd20_2_58 : subd20_2 [1, -3] = true := by decide +kernel
theorem subd20_2_59 : subd20_2 [1, -2] = true := by decide +kernel
theorem subd20_2_60 : subd20_2 [1, -1] = true := by decide +kernel
theorem subd20_2_61 : subd20_2 [1, 0] = true := by decide +kernel
theorem subd20_2_62 : subd20_2 [1, 1] = true := by decide +kernel
theorem subd20_2_63 : subd20_2 [1, 2] = true := by decide +kernel
theorem sbd20_2_1 : ∀ q ∈ blkd20_2_1, subd20_2 q = true := by
  unfold blkd20_2_1
  exact List.forall_mem_cons.2 ⟨subd20_2_32, List.forall_mem_cons.2 ⟨subd20_2_33, List.forall_mem_cons.2 ⟨subd20_2_34, List.forall_mem_cons.2 ⟨subd20_2_35, List.forall_mem_cons.2 ⟨subd20_2_36, List.forall_mem_cons.2 ⟨subd20_2_37, List.forall_mem_cons.2 ⟨subd20_2_38, List.forall_mem_cons.2 ⟨subd20_2_39, List.forall_mem_cons.2 ⟨subd20_2_40, List.forall_mem_cons.2 ⟨subd20_2_41, List.forall_mem_cons.2 ⟨subd20_2_42, List.forall_mem_cons.2 ⟨subd20_2_43, List.forall_mem_cons.2 ⟨subd20_2_44, List.forall_mem_cons.2 ⟨subd20_2_45, List.forall_mem_cons.2 ⟨subd20_2_46, List.forall_mem_cons.2 ⟨subd20_2_47, List.forall_mem_cons.2 ⟨subd20_2_48, List.forall_mem_cons.2 ⟨subd20_2_49, List.forall_mem_cons.2 ⟨subd20_2_50, List.forall_mem_cons.2 ⟨subd20_2_51, List.forall_mem_cons.2 ⟨subd20_2_52, List.forall_mem_cons.2 ⟨subd20_2_53, List.forall_mem_cons.2 ⟨subd20_2_54, List.forall_mem_cons.2 ⟨subd20_2_55, List.forall_mem_cons.2 ⟨subd20_2_56, List.forall_mem_cons.2 ⟨subd20_2_57, List.forall_mem_cons.2 ⟨subd20_2_58, List.forall_mem_cons.2 ⟨subd20_2_59, List.forall_mem_cons.2 ⟨subd20_2_60, List.forall_mem_cons.2 ⟨subd20_2_61, List.forall_mem_cons.2 ⟨subd20_2_62, List.forall_mem_cons.2 ⟨subd20_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
