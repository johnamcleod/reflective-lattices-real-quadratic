import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_32 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [-1, 4] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [0, -5] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [0, 4] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [1, -5] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [2, -5] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [2, -4] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [2, -3] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [2, 0] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [2, 3] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [3, -5] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [3, -4] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [3, -3] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [3, -2] = true := by decide +kernel
theorem subd11_0_66 : subd11_0 [3, -1] = true := by decide +kernel
theorem subd11_0_67 : subd11_0 [3, 0] = true := by decide +kernel
theorem subd11_0_68 : subd11_0 [3, 1] = true := by decide +kernel
theorem subd11_0_69 : subd11_0 [3, 2] = true := by decide +kernel
theorem subd11_0_70 : subd11_0 [4, -5] = true := by decide +kernel
theorem subd11_0_71 : subd11_0 [4, -4] = true := by decide +kernel
theorem subd11_0_72 : subd11_0 [4, -3] = true := by decide +kernel
theorem subd11_0_73 : subd11_0 [4, -2] = true := by decide +kernel
theorem subd11_0_74 : subd11_0 [4, -1] = true := by decide +kernel
theorem subd11_0_75 : subd11_0 [4, 0] = true := by decide +kernel
theorem subd11_0_76 : subd11_0 [4, 1] = true := by decide +kernel
theorem subd11_0_77 : subd11_0 [5] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_cons.2 ⟨subd11_0_66, List.forall_mem_cons.2 ⟨subd11_0_67, List.forall_mem_cons.2 ⟨subd11_0_68, List.forall_mem_cons.2 ⟨subd11_0_69, List.forall_mem_cons.2 ⟨subd11_0_70, List.forall_mem_cons.2 ⟨subd11_0_71, List.forall_mem_cons.2 ⟨subd11_0_72, List.forall_mem_cons.2 ⟨subd11_0_73, List.forall_mem_cons.2 ⟨subd11_0_74, List.forall_mem_cons.2 ⟨subd11_0_75, List.forall_mem_cons.2 ⟨subd11_0_76, List.forall_mem_cons.2 ⟨subd11_0_77, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-4] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-3, -5] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-3, -4] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-3, -3] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-3, -2] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-3, -1] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-3, 0] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-3, 1] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-2, -5] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-2, -4] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-1, -5] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [0, 2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [1, 3] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [1, 4] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [2, 2] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [2, 4] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [3, -2] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [3, -1] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [3, 0] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [3, 1] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [3, 2] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [3, 3] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [3, 4] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [4] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-4] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-3, -4] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-3, -3] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-3, -2] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-3, -1] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-3, 0] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-3, 1] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-3, 2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-3, 3] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-3, 4] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-2, -5] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-2, -4] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-2, 1] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [-2, 3] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [-2, 4] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [-1, -5] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [-1, 4] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [-1, 5] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [0, -6] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
