import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_32 : subd5_2 [0, 0] = true := by decide +kernel
theorem subd5_2_33 : subd5_2 [0, 1] = true := by decide +kernel
theorem subd5_2_34 : subd5_2 [0, 2] = true := by decide +kernel
theorem subd5_2_35 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_36 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_37 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_38 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_39 : subd5_2 [1, -3] = true := by decide +kernel
theorem subd5_2_40 : subd5_2 [1, -2] = true := by decide +kernel
theorem subd5_2_41 : subd5_2 [1, -1] = true := by decide +kernel
theorem subd5_2_42 : subd5_2 [1, 0] = true := by decide +kernel
theorem subd5_2_43 : subd5_2 [1, 1] = true := by decide +kernel
theorem subd5_2_44 : subd5_2 [1, 2] = true := by decide +kernel
theorem subd5_2_45 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_46 : subd5_2 [1, 4] = true := by decide +kernel
theorem subd5_2_47 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_48 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_49 : subd5_2 [2, -2] = true := by decide +kernel
theorem subd5_2_50 : subd5_2 [2, -1] = true := by decide +kernel
theorem subd5_2_51 : subd5_2 [2, 0] = true := by decide +kernel
theorem subd5_2_52 : subd5_2 [2, 1] = true := by decide +kernel
theorem subd5_2_53 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_54 : subd5_2 [2, 3] = true := by decide +kernel
theorem subd5_2_55 : subd5_2 [2, 4] = true := by decide +kernel
theorem subd5_2_56 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_57 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_58 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_59 : subd5_2 [3, 1] = true := by decide +kernel
theorem subd5_2_60 : subd5_2 [3, 2] = true := by decide +kernel
theorem subd5_2_61 : subd5_2 [3, 3] = true := by decide +kernel
theorem subd5_2_62 : subd5_2 [3, 4] = true := by decide +kernel
theorem subd5_2_63 : subd5_2 [4] = true := by decide +kernel
theorem sbd5_2_1 : ∀ q ∈ blkd5_2_1, subd5_2 q = true := by
  unfold blkd5_2_1
  exact List.forall_mem_cons.2 ⟨subd5_2_32, List.forall_mem_cons.2 ⟨subd5_2_33, List.forall_mem_cons.2 ⟨subd5_2_34, List.forall_mem_cons.2 ⟨subd5_2_35, List.forall_mem_cons.2 ⟨subd5_2_36, List.forall_mem_cons.2 ⟨subd5_2_37, List.forall_mem_cons.2 ⟨subd5_2_38, List.forall_mem_cons.2 ⟨subd5_2_39, List.forall_mem_cons.2 ⟨subd5_2_40, List.forall_mem_cons.2 ⟨subd5_2_41, List.forall_mem_cons.2 ⟨subd5_2_42, List.forall_mem_cons.2 ⟨subd5_2_43, List.forall_mem_cons.2 ⟨subd5_2_44, List.forall_mem_cons.2 ⟨subd5_2_45, List.forall_mem_cons.2 ⟨subd5_2_46, List.forall_mem_cons.2 ⟨subd5_2_47, List.forall_mem_cons.2 ⟨subd5_2_48, List.forall_mem_cons.2 ⟨subd5_2_49, List.forall_mem_cons.2 ⟨subd5_2_50, List.forall_mem_cons.2 ⟨subd5_2_51, List.forall_mem_cons.2 ⟨subd5_2_52, List.forall_mem_cons.2 ⟨subd5_2_53, List.forall_mem_cons.2 ⟨subd5_2_54, List.forall_mem_cons.2 ⟨subd5_2_55, List.forall_mem_cons.2 ⟨subd5_2_56, List.forall_mem_cons.2 ⟨subd5_2_57, List.forall_mem_cons.2 ⟨subd5_2_58, List.forall_mem_cons.2 ⟨subd5_2_59, List.forall_mem_cons.2 ⟨subd5_2_60, List.forall_mem_cons.2 ⟨subd5_2_61, List.forall_mem_cons.2 ⟨subd5_2_62, List.forall_mem_cons.2 ⟨subd5_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-3, -3] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-3, -2] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-3, -1] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-3, 0] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-3, 1] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-3, 2] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-2, -4] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [0, -5] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [0, 4] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [1, 3] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [2, -4] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [2, 3] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [3, -3] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [3, -2] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [3, -1] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [3, 0] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [3, 1] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [3, 2] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-3] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-2] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [-1, -3] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [-1, -2] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [-1, -1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [-1, 0] = true := by decide +kernel
theorem subd5_4_6 : subd5_4 [-1, 1] = true := by decide +kernel
theorem subd5_4_7 : subd5_4 [-1, 2] = true := by decide +kernel
theorem subd5_4_8 : subd5_4 [-1, 3] = true := by decide +kernel
theorem subd5_4_9 : subd5_4 [0, -3] = true := by decide +kernel
theorem subd5_4_10 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_11 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_12 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_13 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_14 : subd5_4 [0, 2] = true := by decide +kernel
theorem subd5_4_15 : subd5_4 [1, -4] = true := by decide +kernel
theorem subd5_4_16 : subd5_4 [1, -3] = true := by decide +kernel
theorem subd5_4_17 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_18 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_19 : subd5_4 [1, 0] = true := by decide +kernel
theorem subd5_4_20 : subd5_4 [1, 1] = true := by decide +kernel
theorem subd5_4_21 : subd5_4 [1, 2] = true := by decide +kernel
theorem subd5_4_22 : subd5_4 [2] = true := by decide +kernel
theorem subd5_4_23 : subd5_4 [3] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_cons.2 ⟨subd5_4_6, List.forall_mem_cons.2 ⟨subd5_4_7, List.forall_mem_cons.2 ⟨subd5_4_8, List.forall_mem_cons.2 ⟨subd5_4_9, List.forall_mem_cons.2 ⟨subd5_4_10, List.forall_mem_cons.2 ⟨subd5_4_11, List.forall_mem_cons.2 ⟨subd5_4_12, List.forall_mem_cons.2 ⟨subd5_4_13, List.forall_mem_cons.2 ⟨subd5_4_14, List.forall_mem_cons.2 ⟨subd5_4_15, List.forall_mem_cons.2 ⟨subd5_4_16, List.forall_mem_cons.2 ⟨subd5_4_17, List.forall_mem_cons.2 ⟨subd5_4_18, List.forall_mem_cons.2 ⟨subd5_4_19, List.forall_mem_cons.2 ⟨subd5_4_20, List.forall_mem_cons.2 ⟨subd5_4_21, List.forall_mem_cons.2 ⟨subd5_4_22, List.forall_mem_cons.2 ⟨subd5_4_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
