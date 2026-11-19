import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_0 : subd5_2 [-5] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-4, -2] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-4, -1] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-4, 0] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-4, 1] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-4, 2] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-4, 3] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-4, 4] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-3, -3] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-3, -2] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-3, -1] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-3, 0] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-3, 1] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-3, 2] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-3, 3] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-3, 4] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-3, 5] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-2, -4] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [-2, 4] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [-2, 5] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [-1, 0] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_32 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [-1, 4] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [0, -5] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [2, -6] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [2, -5] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_62 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_63 : subd5_2 [2, 2] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_cons.2 ⟨subd5_2_62, List.forall_mem_cons.2 ⟨subd5_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_64 : subd5_2 [2, 3] = true := by decide +kernel
theorem subd5_2_65 : subd5_2 [3, -6] = true := by decide +kernel
theorem subd5_2_66 : subd5_2 [3, -5] = true := by decide +kernel
theorem subd5_2_67 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_68 : subd5_2 [3, -3] = true := by decide +kernel
theorem subd5_2_69 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_70 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_71 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_72 : subd5_2 [3, 1] = true := by decide +kernel
theorem subd5_2_73 : subd5_2 [3, 2] = true := by decide +kernel
theorem subd5_2_74 : subd5_2 [4, -5] = true := by decide +kernel
theorem subd5_2_75 : subd5_2 [4, -4] = true := by decide +kernel
theorem subd5_2_76 : subd5_2 [4, -3] = true := by decide +kernel
theorem subd5_2_77 : subd5_2 [4, -2] = true := by decide +kernel
theorem subd5_2_78 : subd5_2 [4, -1] = true := by decide +kernel
theorem subd5_2_79 : subd5_2 [4, 0] = true := by decide +kernel
theorem subd5_2_80 : subd5_2 [4, 1] = true := by decide +kernel
theorem subd5_2_81 : subd5_2 [5] = true := by decide +kernel
theorem sbd5_2_2 : ∀ q ∈ blkd5_2_2, subd5_2 q = true := by
  unfold blkd5_2_2
  exact List.forall_mem_cons.2 ⟨subd5_2_64, List.forall_mem_cons.2 ⟨subd5_2_65, List.forall_mem_cons.2 ⟨subd5_2_66, List.forall_mem_cons.2 ⟨subd5_2_67, List.forall_mem_cons.2 ⟨subd5_2_68, List.forall_mem_cons.2 ⟨subd5_2_69, List.forall_mem_cons.2 ⟨subd5_2_70, List.forall_mem_cons.2 ⟨subd5_2_71, List.forall_mem_cons.2 ⟨subd5_2_72, List.forall_mem_cons.2 ⟨subd5_2_73, List.forall_mem_cons.2 ⟨subd5_2_74, List.forall_mem_cons.2 ⟨subd5_2_75, List.forall_mem_cons.2 ⟨subd5_2_76, List.forall_mem_cons.2 ⟨subd5_2_77, List.forall_mem_cons.2 ⟨subd5_2_78, List.forall_mem_cons.2 ⟨subd5_2_79, List.forall_mem_cons.2 ⟨subd5_2_80, List.forall_mem_cons.2 ⟨subd5_2_81, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-2] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [2] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-3] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-2, -4] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-2, -3] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-2, -2] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-2, -1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-2, 0] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-2, 1] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-2, 2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-1, -4] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [-1, -3] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [-1, -1] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [-1, 0] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [-1, 3] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [0, -4] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [0, 3] = true := by decide +kernel
theorem subd5_4_24 : subd5_4 [1, -4] = true := by decide +kernel
theorem subd5_4_25 : subd5_4 [1, -3] = true := by decide +kernel
theorem subd5_4_26 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_27 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_28 : subd5_4 [1, 0] = true := by decide +kernel
theorem subd5_4_29 : subd5_4 [1, 1] = true := by decide +kernel
theorem subd5_4_30 : subd5_4 [1, 2] = true := by decide +kernel
theorem subd5_4_31 : subd5_4 [1, 3] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_cons.2 ⟨subd5_4_24, List.forall_mem_cons.2 ⟨subd5_4_25, List.forall_mem_cons.2 ⟨subd5_4_26, List.forall_mem_cons.2 ⟨subd5_4_27, List.forall_mem_cons.2 ⟨subd5_4_28, List.forall_mem_cons.2 ⟨subd5_4_29, List.forall_mem_cons.2 ⟨subd5_4_30, List.forall_mem_cons.2 ⟨subd5_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_4_32 : subd5_4 [2, -3] = true := by decide +kernel
theorem subd5_4_33 : subd5_4 [2, -2] = true := by decide +kernel
theorem subd5_4_34 : subd5_4 [2, -1] = true := by decide +kernel
theorem subd5_4_35 : subd5_4 [2, 0] = true := by decide +kernel
theorem subd5_4_36 : subd5_4 [2, 1] = true := by decide +kernel
theorem subd5_4_37 : subd5_4 [2, 2] = true := by decide +kernel
theorem subd5_4_38 : subd5_4 [2, 3] = true := by decide +kernel
theorem subd5_4_39 : subd5_4 [3] = true := by decide +kernel
theorem sbd5_4_1 : ∀ q ∈ blkd5_4_1, subd5_4 q = true := by
  unfold blkd5_4_1
  exact List.forall_mem_cons.2 ⟨subd5_4_32, List.forall_mem_cons.2 ⟨subd5_4_33, List.forall_mem_cons.2 ⟨subd5_4_34, List.forall_mem_cons.2 ⟨subd5_4_35, List.forall_mem_cons.2 ⟨subd5_4_36, List.forall_mem_cons.2 ⟨subd5_4_37, List.forall_mem_cons.2 ⟨subd5_4_38, List.forall_mem_cons.2 ⟨subd5_4_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C099
