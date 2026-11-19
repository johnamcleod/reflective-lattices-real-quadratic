import ReflectZphi.Data.Cert5.C139.Base

namespace ReflectZphi.Data.Cert5.C139

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_0 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-1, 0, -7] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-1, 0, -6] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-1, 0, -5] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-1, 0, -4] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-1, 0, -3] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-1, 0, -2] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-1, 0, -1] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-1, 0, 0] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-1, 0, 1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-1, 0, 2] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-1, 0, 3] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-1, 0, 4] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-1, 0, 5] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-1, 0, 6] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [0, -1, -7] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [0, -1, -6] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [0, -1, -5] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [0, -1, -4] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [0, -1, -3] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [0, -1, -2] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [0, -1, -1] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [0, -1, 0] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [0, -1, 1] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [0, -1, 2] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [0, -1, 3] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [0, -1, 4] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [0, -1, 5] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [0, 0, -8] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_32 : subd10_3 [0, 0, -7] = true := by decide +kernel
theorem subd10_3_33 : subd10_3 [0, 0, -6] = true := by decide +kernel
theorem subd10_3_34 : subd10_3 [0, 0, -5] = true := by decide +kernel
theorem subd10_3_35 : subd10_3 [0, 0, -4] = true := by decide +kernel
theorem subd10_3_36 : subd10_3 [0, 0, -3] = true := by decide +kernel
theorem subd10_3_37 : subd10_3 [0, 0, -2] = true := by decide +kernel
theorem subd10_3_38 : subd10_3 [0, 0, -1] = true := by decide +kernel
theorem subd10_3_39 : subd10_3 [0, 0, 0] = true := by decide +kernel
theorem subd10_3_40 : subd10_3 [0, 0, 1] = true := by decide +kernel
theorem subd10_3_41 : subd10_3 [0, 0, 2] = true := by decide +kernel
theorem subd10_3_42 : subd10_3 [0, 0, 3] = true := by decide +kernel
theorem subd10_3_43 : subd10_3 [0, 0, 4] = true := by decide +kernel
theorem subd10_3_44 : subd10_3 [0, 0, 5] = true := by decide +kernel
theorem subd10_3_45 : subd10_3 [0, 0, 6] = true := by decide +kernel
theorem subd10_3_46 : subd10_3 [0, 0, 7] = true := by decide +kernel
theorem subd10_3_47 : subd10_3 [0, 1, -6] = true := by decide +kernel
theorem subd10_3_48 : subd10_3 [0, 1, -5] = true := by decide +kernel
theorem subd10_3_49 : subd10_3 [0, 1, -4] = true := by decide +kernel
theorem subd10_3_50 : subd10_3 [0, 1, -3] = true := by decide +kernel
theorem subd10_3_51 : subd10_3 [0, 1, -2] = true := by decide +kernel
theorem subd10_3_52 : subd10_3 [0, 1, -1] = true := by decide +kernel
theorem subd10_3_53 : subd10_3 [0, 1, 0] = true := by decide +kernel
theorem subd10_3_54 : subd10_3 [0, 1, 1] = true := by decide +kernel
theorem subd10_3_55 : subd10_3 [0, 1, 2] = true := by decide +kernel
theorem subd10_3_56 : subd10_3 [0, 1, 3] = true := by decide +kernel
theorem subd10_3_57 : subd10_3 [0, 1, 4] = true := by decide +kernel
theorem subd10_3_58 : subd10_3 [0, 1, 5] = true := by decide +kernel
theorem subd10_3_59 : subd10_3 [0, 1, 6] = true := by decide +kernel
theorem subd10_3_60 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_61 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_62 : subd10_3 [1, 0, -7] = true := by decide +kernel
theorem subd10_3_63 : subd10_3 [1, 0, -6] = true := by decide +kernel
theorem sbd10_3_1 : ∀ q ∈ blkd10_3_1, subd10_3 q = true := by
  unfold blkd10_3_1
  exact List.forall_mem_cons.2 ⟨subd10_3_32, List.forall_mem_cons.2 ⟨subd10_3_33, List.forall_mem_cons.2 ⟨subd10_3_34, List.forall_mem_cons.2 ⟨subd10_3_35, List.forall_mem_cons.2 ⟨subd10_3_36, List.forall_mem_cons.2 ⟨subd10_3_37, List.forall_mem_cons.2 ⟨subd10_3_38, List.forall_mem_cons.2 ⟨subd10_3_39, List.forall_mem_cons.2 ⟨subd10_3_40, List.forall_mem_cons.2 ⟨subd10_3_41, List.forall_mem_cons.2 ⟨subd10_3_42, List.forall_mem_cons.2 ⟨subd10_3_43, List.forall_mem_cons.2 ⟨subd10_3_44, List.forall_mem_cons.2 ⟨subd10_3_45, List.forall_mem_cons.2 ⟨subd10_3_46, List.forall_mem_cons.2 ⟨subd10_3_47, List.forall_mem_cons.2 ⟨subd10_3_48, List.forall_mem_cons.2 ⟨subd10_3_49, List.forall_mem_cons.2 ⟨subd10_3_50, List.forall_mem_cons.2 ⟨subd10_3_51, List.forall_mem_cons.2 ⟨subd10_3_52, List.forall_mem_cons.2 ⟨subd10_3_53, List.forall_mem_cons.2 ⟨subd10_3_54, List.forall_mem_cons.2 ⟨subd10_3_55, List.forall_mem_cons.2 ⟨subd10_3_56, List.forall_mem_cons.2 ⟨subd10_3_57, List.forall_mem_cons.2 ⟨subd10_3_58, List.forall_mem_cons.2 ⟨subd10_3_59, List.forall_mem_cons.2 ⟨subd10_3_60, List.forall_mem_cons.2 ⟨subd10_3_61, List.forall_mem_cons.2 ⟨subd10_3_62, List.forall_mem_cons.2 ⟨subd10_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_64 : subd10_3 [1, 0, -5] = true := by decide +kernel
theorem subd10_3_65 : subd10_3 [1, 0, -4] = true := by decide +kernel
theorem subd10_3_66 : subd10_3 [1, 0, -3] = true := by decide +kernel
theorem subd10_3_67 : subd10_3 [1, 0, -2] = true := by decide +kernel
theorem subd10_3_68 : subd10_3 [1, 0, -1] = true := by decide +kernel
theorem subd10_3_69 : subd10_3 [1, 0, 0] = true := by decide +kernel
theorem subd10_3_70 : subd10_3 [1, 0, 1] = true := by decide +kernel
theorem subd10_3_71 : subd10_3 [1, 0, 2] = true := by decide +kernel
theorem subd10_3_72 : subd10_3 [1, 0, 3] = true := by decide +kernel
theorem subd10_3_73 : subd10_3 [1, 0, 4] = true := by decide +kernel
theorem subd10_3_74 : subd10_3 [1, 0, 5] = true := by decide +kernel
theorem subd10_3_75 : subd10_3 [1, 0, 6] = true := by decide +kernel
theorem subd10_3_76 : subd10_3 [1, 1] = true := by decide +kernel
theorem sbd10_3_2 : ∀ q ∈ blkd10_3_2, subd10_3 q = true := by
  unfold blkd10_3_2
  exact List.forall_mem_cons.2 ⟨subd10_3_64, List.forall_mem_cons.2 ⟨subd10_3_65, List.forall_mem_cons.2 ⟨subd10_3_66, List.forall_mem_cons.2 ⟨subd10_3_67, List.forall_mem_cons.2 ⟨subd10_3_68, List.forall_mem_cons.2 ⟨subd10_3_69, List.forall_mem_cons.2 ⟨subd10_3_70, List.forall_mem_cons.2 ⟨subd10_3_71, List.forall_mem_cons.2 ⟨subd10_3_72, List.forall_mem_cons.2 ⟨subd10_3_73, List.forall_mem_cons.2 ⟨subd10_3_74, List.forall_mem_cons.2 ⟨subd10_3_75, List.forall_mem_cons.2 ⟨subd10_3_76, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [0] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [1] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-2, 3] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [2, -4] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [2, -2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [1] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C139
