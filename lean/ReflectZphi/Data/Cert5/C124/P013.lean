import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_12 : ldCheck G d5_12.U d5_12.ms ldd5_12 = true := by decide +kernel
theorem pre_okd5_12 : subPre G cell5 d5_12 = true := by decide +kernel
theorem subd5_12_0 : subd5_12 [-2] = true := by decide +kernel
theorem subd5_12_1 : subd5_12 [-1, -3] = true := by decide +kernel
theorem subd5_12_2 : subd5_12 [-1, -2] = true := by decide +kernel
theorem subd5_12_3 : subd5_12 [-1, -1] = true := by decide +kernel
theorem subd5_12_4 : subd5_12 [-1, 0] = true := by decide +kernel
theorem subd5_12_5 : subd5_12 [-1, 1] = true := by decide +kernel
theorem subd5_12_6 : subd5_12 [0, -3] = true := by decide +kernel
theorem subd5_12_7 : subd5_12 [0, -2] = true := by decide +kernel
theorem subd5_12_8 : subd5_12 [0, -1] = true := by decide +kernel
theorem subd5_12_9 : subd5_12 [0, 0] = true := by decide +kernel
theorem subd5_12_10 : subd5_12 [0, 1] = true := by decide +kernel
theorem subd5_12_11 : subd5_12 [0, 2] = true := by decide +kernel
theorem subd5_12_12 : subd5_12 [1, -2] = true := by decide +kernel
theorem subd5_12_13 : subd5_12 [1, -1] = true := by decide +kernel
theorem subd5_12_14 : subd5_12 [1, 0] = true := by decide +kernel
theorem subd5_12_15 : subd5_12 [1, 1] = true := by decide +kernel
theorem subd5_12_16 : subd5_12 [1, 2] = true := by decide +kernel
theorem subd5_12_17 : subd5_12 [2] = true := by decide +kernel
theorem sbd5_12_0 : ∀ q ∈ blkd5_12_0, subd5_12 q = true := by
  unfold blkd5_12_0
  exact List.forall_mem_cons.2 ⟨subd5_12_0, List.forall_mem_cons.2 ⟨subd5_12_1, List.forall_mem_cons.2 ⟨subd5_12_2, List.forall_mem_cons.2 ⟨subd5_12_3, List.forall_mem_cons.2 ⟨subd5_12_4, List.forall_mem_cons.2 ⟨subd5_12_5, List.forall_mem_cons.2 ⟨subd5_12_6, List.forall_mem_cons.2 ⟨subd5_12_7, List.forall_mem_cons.2 ⟨subd5_12_8, List.forall_mem_cons.2 ⟨subd5_12_9, List.forall_mem_cons.2 ⟨subd5_12_10, List.forall_mem_cons.2 ⟨subd5_12_11, List.forall_mem_cons.2 ⟨subd5_12_12, List.forall_mem_cons.2 ⟨subd5_12_13, List.forall_mem_cons.2 ⟨subd5_12_14, List.forall_mem_cons.2 ⟨subd5_12_15, List.forall_mem_cons.2 ⟨subd5_12_16, List.forall_mem_cons.2 ⟨subd5_12_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_13 : ldCheck G d5_13.U d5_13.ms ldd5_13 = true := by decide +kernel
theorem pre_okd5_13 : subPre G cell5 d5_13 = true := by decide +kernel
theorem subd5_13_0 : subd5_13 [-3] = true := by decide +kernel
theorem subd5_13_1 : subd5_13 [-2] = true := by decide +kernel
theorem subd5_13_2 : subd5_13 [-1] = true := by decide +kernel
theorem subd5_13_3 : subd5_13 [0] = true := by decide +kernel
theorem subd5_13_4 : subd5_13 [1] = true := by decide +kernel
theorem subd5_13_5 : subd5_13 [2] = true := by decide +kernel
theorem subd5_13_6 : subd5_13 [3] = true := by decide +kernel
theorem sbd5_13_0 : ∀ q ∈ blkd5_13_0, subd5_13 q = true := by
  unfold blkd5_13_0
  exact List.forall_mem_cons.2 ⟨subd5_13_0, List.forall_mem_cons.2 ⟨subd5_13_1, List.forall_mem_cons.2 ⟨subd5_13_2, List.forall_mem_cons.2 ⟨subd5_13_3, List.forall_mem_cons.2 ⟨subd5_13_4, List.forall_mem_cons.2 ⟨subd5_13_5, List.forall_mem_cons.2 ⟨subd5_13_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_14 : ldCheck G d5_14.U d5_14.ms ldd5_14 = true := by decide +kernel
theorem pre_okd5_14 : subPre G cell5 d5_14 = true := by decide +kernel
theorem subd5_14_0 : subd5_14 [-5] = true := by decide +kernel
theorem subd5_14_1 : subd5_14 [-4, -3] = true := by decide +kernel
theorem subd5_14_2 : subd5_14 [-4, -2] = true := by decide +kernel
theorem subd5_14_3 : subd5_14 [-4, -1] = true := by decide +kernel
theorem subd5_14_4 : subd5_14 [-4, 0] = true := by decide +kernel
theorem subd5_14_5 : subd5_14 [-4, 1] = true := by decide +kernel
theorem subd5_14_6 : subd5_14 [-4, 2] = true := by decide +kernel
theorem subd5_14_7 : subd5_14 [-4, 3] = true := by decide +kernel
theorem subd5_14_8 : subd5_14 [-3, -4] = true := by decide +kernel
theorem subd5_14_9 : subd5_14 [-3, -3] = true := by decide +kernel
theorem subd5_14_10 : subd5_14 [-3, -2] = true := by decide +kernel
theorem subd5_14_11 : subd5_14 [-3, -1] = true := by decide +kernel
theorem subd5_14_12 : subd5_14 [-3, 0] = true := by decide +kernel
theorem subd5_14_13 : subd5_14 [-3, 1] = true := by decide +kernel
theorem subd5_14_14 : subd5_14 [-3, 2] = true := by decide +kernel
theorem subd5_14_15 : subd5_14 [-3, 3] = true := by decide +kernel
theorem subd5_14_16 : subd5_14 [-3, 4] = true := by decide +kernel
theorem subd5_14_17 : subd5_14 [-2, -4] = true := by decide +kernel
theorem subd5_14_18 : subd5_14 [-2, -3] = true := by decide +kernel
theorem subd5_14_19 : subd5_14 [-2, -2] = true := by decide +kernel
theorem subd5_14_20 : subd5_14 [-2, -1] = true := by decide +kernel
theorem subd5_14_21 : subd5_14 [-2, 0] = true := by decide +kernel
theorem subd5_14_22 : subd5_14 [-2, 1] = true := by decide +kernel
theorem subd5_14_23 : subd5_14 [-2, 2] = true := by decide +kernel
theorem subd5_14_24 : subd5_14 [-2, 3] = true := by decide +kernel
theorem subd5_14_25 : subd5_14 [-2, 4] = true := by decide +kernel
theorem subd5_14_26 : subd5_14 [-1, -5] = true := by decide +kernel
theorem subd5_14_27 : subd5_14 [-1, -4] = true := by decide +kernel
theorem subd5_14_28 : subd5_14 [-1, -3] = true := by decide +kernel
theorem subd5_14_29 : subd5_14 [-1, -2] = true := by decide +kernel
theorem subd5_14_30 : subd5_14 [-1, -1] = true := by decide +kernel
theorem subd5_14_31 : subd5_14 [-1, 0] = true := by decide +kernel
theorem sbd5_14_0 : ∀ q ∈ blkd5_14_0, subd5_14 q = true := by
  unfold blkd5_14_0
  exact List.forall_mem_cons.2 ⟨subd5_14_0, List.forall_mem_cons.2 ⟨subd5_14_1, List.forall_mem_cons.2 ⟨subd5_14_2, List.forall_mem_cons.2 ⟨subd5_14_3, List.forall_mem_cons.2 ⟨subd5_14_4, List.forall_mem_cons.2 ⟨subd5_14_5, List.forall_mem_cons.2 ⟨subd5_14_6, List.forall_mem_cons.2 ⟨subd5_14_7, List.forall_mem_cons.2 ⟨subd5_14_8, List.forall_mem_cons.2 ⟨subd5_14_9, List.forall_mem_cons.2 ⟨subd5_14_10, List.forall_mem_cons.2 ⟨subd5_14_11, List.forall_mem_cons.2 ⟨subd5_14_12, List.forall_mem_cons.2 ⟨subd5_14_13, List.forall_mem_cons.2 ⟨subd5_14_14, List.forall_mem_cons.2 ⟨subd5_14_15, List.forall_mem_cons.2 ⟨subd5_14_16, List.forall_mem_cons.2 ⟨subd5_14_17, List.forall_mem_cons.2 ⟨subd5_14_18, List.forall_mem_cons.2 ⟨subd5_14_19, List.forall_mem_cons.2 ⟨subd5_14_20, List.forall_mem_cons.2 ⟨subd5_14_21, List.forall_mem_cons.2 ⟨subd5_14_22, List.forall_mem_cons.2 ⟨subd5_14_23, List.forall_mem_cons.2 ⟨subd5_14_24, List.forall_mem_cons.2 ⟨subd5_14_25, List.forall_mem_cons.2 ⟨subd5_14_26, List.forall_mem_cons.2 ⟨subd5_14_27, List.forall_mem_cons.2 ⟨subd5_14_28, List.forall_mem_cons.2 ⟨subd5_14_29, List.forall_mem_cons.2 ⟨subd5_14_30, List.forall_mem_cons.2 ⟨subd5_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_14_32 : subd5_14 [-1, 1] = true := by decide +kernel
theorem subd5_14_33 : subd5_14 [-1, 2] = true := by decide +kernel
theorem subd5_14_34 : subd5_14 [-1, 3] = true := by decide +kernel
theorem subd5_14_35 : subd5_14 [-1, 4] = true := by decide +kernel
theorem subd5_14_36 : subd5_14 [0, -5] = true := by decide +kernel
theorem subd5_14_37 : subd5_14 [0, -4] = true := by decide +kernel
theorem subd5_14_38 : subd5_14 [0, -3] = true := by decide +kernel
theorem subd5_14_39 : subd5_14 [0, -2] = true := by decide +kernel
theorem subd5_14_40 : subd5_14 [0, -1] = true := by decide +kernel
theorem subd5_14_41 : subd5_14 [0, 0] = true := by decide +kernel
theorem subd5_14_42 : subd5_14 [0, 1] = true := by decide +kernel
theorem subd5_14_43 : subd5_14 [0, 2] = true := by decide +kernel
theorem subd5_14_44 : subd5_14 [0, 3] = true := by decide +kernel
theorem subd5_14_45 : subd5_14 [0, 4] = true := by decide +kernel
theorem subd5_14_46 : subd5_14 [1, -5] = true := by decide +kernel
theorem subd5_14_47 : subd5_14 [1, -4] = true := by decide +kernel
theorem subd5_14_48 : subd5_14 [1, -3] = true := by decide +kernel
theorem subd5_14_49 : subd5_14 [1, -2] = true := by decide +kernel
theorem subd5_14_50 : subd5_14 [1, -1] = true := by decide +kernel
theorem subd5_14_51 : subd5_14 [1, 0] = true := by decide +kernel
theorem subd5_14_52 : subd5_14 [1, 1] = true := by decide +kernel
theorem subd5_14_53 : subd5_14 [1, 2] = true := by decide +kernel
theorem subd5_14_54 : subd5_14 [1, 3] = true := by decide +kernel
theorem subd5_14_55 : subd5_14 [1, 4] = true := by decide +kernel
theorem subd5_14_56 : subd5_14 [2, -5] = true := by decide +kernel
theorem subd5_14_57 : subd5_14 [2, -4] = true := by decide +kernel
theorem subd5_14_58 : subd5_14 [2, -3] = true := by decide +kernel
theorem subd5_14_59 : subd5_14 [2, -2] = true := by decide +kernel
theorem subd5_14_60 : subd5_14 [2, -1] = true := by decide +kernel
theorem subd5_14_61 : subd5_14 [2, 0] = true := by decide +kernel
theorem subd5_14_62 : subd5_14 [2, 1] = true := by decide +kernel
theorem subd5_14_63 : subd5_14 [2, 2] = true := by decide +kernel
theorem sbd5_14_1 : ∀ q ∈ blkd5_14_1, subd5_14 q = true := by
  unfold blkd5_14_1
  exact List.forall_mem_cons.2 ⟨subd5_14_32, List.forall_mem_cons.2 ⟨subd5_14_33, List.forall_mem_cons.2 ⟨subd5_14_34, List.forall_mem_cons.2 ⟨subd5_14_35, List.forall_mem_cons.2 ⟨subd5_14_36, List.forall_mem_cons.2 ⟨subd5_14_37, List.forall_mem_cons.2 ⟨subd5_14_38, List.forall_mem_cons.2 ⟨subd5_14_39, List.forall_mem_cons.2 ⟨subd5_14_40, List.forall_mem_cons.2 ⟨subd5_14_41, List.forall_mem_cons.2 ⟨subd5_14_42, List.forall_mem_cons.2 ⟨subd5_14_43, List.forall_mem_cons.2 ⟨subd5_14_44, List.forall_mem_cons.2 ⟨subd5_14_45, List.forall_mem_cons.2 ⟨subd5_14_46, List.forall_mem_cons.2 ⟨subd5_14_47, List.forall_mem_cons.2 ⟨subd5_14_48, List.forall_mem_cons.2 ⟨subd5_14_49, List.forall_mem_cons.2 ⟨subd5_14_50, List.forall_mem_cons.2 ⟨subd5_14_51, List.forall_mem_cons.2 ⟨subd5_14_52, List.forall_mem_cons.2 ⟨subd5_14_53, List.forall_mem_cons.2 ⟨subd5_14_54, List.forall_mem_cons.2 ⟨subd5_14_55, List.forall_mem_cons.2 ⟨subd5_14_56, List.forall_mem_cons.2 ⟨subd5_14_57, List.forall_mem_cons.2 ⟨subd5_14_58, List.forall_mem_cons.2 ⟨subd5_14_59, List.forall_mem_cons.2 ⟨subd5_14_60, List.forall_mem_cons.2 ⟨subd5_14_61, List.forall_mem_cons.2 ⟨subd5_14_62, List.forall_mem_cons.2 ⟨subd5_14_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_14_64 : subd5_14 [2, 3] = true := by decide +kernel
theorem subd5_14_65 : subd5_14 [3, -5] = true := by decide +kernel
theorem subd5_14_66 : subd5_14 [3, -4] = true := by decide +kernel
theorem subd5_14_67 : subd5_14 [3, -3] = true := by decide +kernel
theorem subd5_14_68 : subd5_14 [3, -2] = true := by decide +kernel
theorem subd5_14_69 : subd5_14 [3, -1] = true := by decide +kernel
theorem subd5_14_70 : subd5_14 [3, 0] = true := by decide +kernel
theorem subd5_14_71 : subd5_14 [3, 1] = true := by decide +kernel
theorem subd5_14_72 : subd5_14 [3, 2] = true := by decide +kernel
theorem subd5_14_73 : subd5_14 [3, 3] = true := by decide +kernel
theorem subd5_14_74 : subd5_14 [4, -4] = true := by decide +kernel
theorem subd5_14_75 : subd5_14 [4, -3] = true := by decide +kernel
theorem subd5_14_76 : subd5_14 [4, -2] = true := by decide +kernel
theorem subd5_14_77 : subd5_14 [4, -1] = true := by decide +kernel
theorem subd5_14_78 : subd5_14 [4, 0] = true := by decide +kernel
theorem subd5_14_79 : subd5_14 [4, 1] = true := by decide +kernel
theorem subd5_14_80 : subd5_14 [4, 2] = true := by decide +kernel
theorem subd5_14_81 : subd5_14 [5] = true := by decide +kernel
theorem sbd5_14_2 : ∀ q ∈ blkd5_14_2, subd5_14 q = true := by
  unfold blkd5_14_2
  exact List.forall_mem_cons.2 ⟨subd5_14_64, List.forall_mem_cons.2 ⟨subd5_14_65, List.forall_mem_cons.2 ⟨subd5_14_66, List.forall_mem_cons.2 ⟨subd5_14_67, List.forall_mem_cons.2 ⟨subd5_14_68, List.forall_mem_cons.2 ⟨subd5_14_69, List.forall_mem_cons.2 ⟨subd5_14_70, List.forall_mem_cons.2 ⟨subd5_14_71, List.forall_mem_cons.2 ⟨subd5_14_72, List.forall_mem_cons.2 ⟨subd5_14_73, List.forall_mem_cons.2 ⟨subd5_14_74, List.forall_mem_cons.2 ⟨subd5_14_75, List.forall_mem_cons.2 ⟨subd5_14_76, List.forall_mem_cons.2 ⟨subd5_14_77, List.forall_mem_cons.2 ⟨subd5_14_78, List.forall_mem_cons.2 ⟨subd5_14_79, List.forall_mem_cons.2 ⟨subd5_14_80, List.forall_mem_cons.2 ⟨subd5_14_81, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
