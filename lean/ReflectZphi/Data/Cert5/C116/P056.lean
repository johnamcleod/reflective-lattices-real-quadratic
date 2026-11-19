import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_1_0 : subd13_1 [-4] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-3, -6] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-3, -5] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-3, -4] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-3, -3] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-3, -2] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [-3, -1] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [-3, 0] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [-3, 1] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [-3, 2] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [-2, -6] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [-2, -5] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [-2, -4] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [-2, -3] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [-2, -2] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [-2, -1] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [-2, 0] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [-2, 1] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [-2, 2] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [-2, 3] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [-1, -6] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [-1, -5] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [-1, -4] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [-1, -3] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [-1, -2] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [-1, -1] = true := by decide +kernel
theorem subd13_1_26 : subd13_1 [-1, 0] = true := by decide +kernel
theorem subd13_1_27 : subd13_1 [-1, 1] = true := by decide +kernel
theorem subd13_1_28 : subd13_1 [-1, 2] = true := by decide +kernel
theorem subd13_1_29 : subd13_1 [-1, 3] = true := by decide +kernel
theorem subd13_1_30 : subd13_1 [-1, 4] = true := by decide +kernel
theorem subd13_1_31 : subd13_1 [0, -6] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_cons.2 ⟨subd13_1_26, List.forall_mem_cons.2 ⟨subd13_1_27, List.forall_mem_cons.2 ⟨subd13_1_28, List.forall_mem_cons.2 ⟨subd13_1_29, List.forall_mem_cons.2 ⟨subd13_1_30, List.forall_mem_cons.2 ⟨subd13_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_32 : subd13_1 [0, -5] = true := by decide +kernel
theorem subd13_1_33 : subd13_1 [0, -4] = true := by decide +kernel
theorem subd13_1_34 : subd13_1 [0, -3] = true := by decide +kernel
theorem subd13_1_35 : subd13_1 [0, -2] = true := by decide +kernel
theorem subd13_1_36 : subd13_1 [0, -1] = true := by decide +kernel
theorem subd13_1_37 : subd13_1 [0, 0] = true := by decide +kernel
theorem subd13_1_38 : subd13_1 [0, 1] = true := by decide +kernel
theorem subd13_1_39 : subd13_1 [0, 2] = true := by decide +kernel
theorem subd13_1_40 : subd13_1 [0, 3] = true := by decide +kernel
theorem subd13_1_41 : subd13_1 [0, 4] = true := by decide +kernel
theorem subd13_1_42 : subd13_1 [0, 5] = true := by decide +kernel
theorem subd13_1_43 : subd13_1 [1, -5] = true := by decide +kernel
theorem subd13_1_44 : subd13_1 [1, -4] = true := by decide +kernel
theorem subd13_1_45 : subd13_1 [1, -3] = true := by decide +kernel
theorem subd13_1_46 : subd13_1 [1, -2] = true := by decide +kernel
theorem subd13_1_47 : subd13_1 [1, -1] = true := by decide +kernel
theorem subd13_1_48 : subd13_1 [1, 0] = true := by decide +kernel
theorem subd13_1_49 : subd13_1 [1, 1] = true := by decide +kernel
theorem subd13_1_50 : subd13_1 [1, 2] = true := by decide +kernel
theorem subd13_1_51 : subd13_1 [1, 3] = true := by decide +kernel
theorem subd13_1_52 : subd13_1 [1, 4] = true := by decide +kernel
theorem subd13_1_53 : subd13_1 [1, 5] = true := by decide +kernel
theorem subd13_1_54 : subd13_1 [2, -4] = true := by decide +kernel
theorem subd13_1_55 : subd13_1 [2, -3] = true := by decide +kernel
theorem subd13_1_56 : subd13_1 [2, -2] = true := by decide +kernel
theorem subd13_1_57 : subd13_1 [2, -1] = true := by decide +kernel
theorem subd13_1_58 : subd13_1 [2, 0] = true := by decide +kernel
theorem subd13_1_59 : subd13_1 [2, 1] = true := by decide +kernel
theorem subd13_1_60 : subd13_1 [2, 2] = true := by decide +kernel
theorem subd13_1_61 : subd13_1 [2, 3] = true := by decide +kernel
theorem subd13_1_62 : subd13_1 [2, 4] = true := by decide +kernel
theorem subd13_1_63 : subd13_1 [2, 5] = true := by decide +kernel
theorem sbd13_1_1 : ∀ q ∈ blkd13_1_1, subd13_1 q = true := by
  unfold blkd13_1_1
  exact List.forall_mem_cons.2 ⟨subd13_1_32, List.forall_mem_cons.2 ⟨subd13_1_33, List.forall_mem_cons.2 ⟨subd13_1_34, List.forall_mem_cons.2 ⟨subd13_1_35, List.forall_mem_cons.2 ⟨subd13_1_36, List.forall_mem_cons.2 ⟨subd13_1_37, List.forall_mem_cons.2 ⟨subd13_1_38, List.forall_mem_cons.2 ⟨subd13_1_39, List.forall_mem_cons.2 ⟨subd13_1_40, List.forall_mem_cons.2 ⟨subd13_1_41, List.forall_mem_cons.2 ⟨subd13_1_42, List.forall_mem_cons.2 ⟨subd13_1_43, List.forall_mem_cons.2 ⟨subd13_1_44, List.forall_mem_cons.2 ⟨subd13_1_45, List.forall_mem_cons.2 ⟨subd13_1_46, List.forall_mem_cons.2 ⟨subd13_1_47, List.forall_mem_cons.2 ⟨subd13_1_48, List.forall_mem_cons.2 ⟨subd13_1_49, List.forall_mem_cons.2 ⟨subd13_1_50, List.forall_mem_cons.2 ⟨subd13_1_51, List.forall_mem_cons.2 ⟨subd13_1_52, List.forall_mem_cons.2 ⟨subd13_1_53, List.forall_mem_cons.2 ⟨subd13_1_54, List.forall_mem_cons.2 ⟨subd13_1_55, List.forall_mem_cons.2 ⟨subd13_1_56, List.forall_mem_cons.2 ⟨subd13_1_57, List.forall_mem_cons.2 ⟨subd13_1_58, List.forall_mem_cons.2 ⟨subd13_1_59, List.forall_mem_cons.2 ⟨subd13_1_60, List.forall_mem_cons.2 ⟨subd13_1_61, List.forall_mem_cons.2 ⟨subd13_1_62, List.forall_mem_cons.2 ⟨subd13_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_64 : subd13_1 [3, -3] = true := by decide +kernel
theorem subd13_1_65 : subd13_1 [3, -2] = true := by decide +kernel
theorem subd13_1_66 : subd13_1 [3, -1] = true := by decide +kernel
theorem subd13_1_67 : subd13_1 [3, 0] = true := by decide +kernel
theorem subd13_1_68 : subd13_1 [3, 1] = true := by decide +kernel
theorem subd13_1_69 : subd13_1 [3, 2] = true := by decide +kernel
theorem subd13_1_70 : subd13_1 [3, 3] = true := by decide +kernel
theorem subd13_1_71 : subd13_1 [3, 4] = true := by decide +kernel
theorem subd13_1_72 : subd13_1 [3, 5] = true := by decide +kernel
theorem subd13_1_73 : subd13_1 [4] = true := by decide +kernel
theorem sbd13_1_2 : ∀ q ∈ blkd13_1_2, subd13_1 q = true := by
  unfold blkd13_1_2
  exact List.forall_mem_cons.2 ⟨subd13_1_64, List.forall_mem_cons.2 ⟨subd13_1_65, List.forall_mem_cons.2 ⟨subd13_1_66, List.forall_mem_cons.2 ⟨subd13_1_67, List.forall_mem_cons.2 ⟨subd13_1_68, List.forall_mem_cons.2 ⟨subd13_1_69, List.forall_mem_cons.2 ⟨subd13_1_70, List.forall_mem_cons.2 ⟨subd13_1_71, List.forall_mem_cons.2 ⟨subd13_1_72, List.forall_mem_cons.2 ⟨subd13_1_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-1] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [0] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [1] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-5] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-4, -4] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [-4, -3] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [-4, -2] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [-4, -1] = true := by decide +kernel
theorem subd14_1_5 : subd14_1 [-4, 0] = true := by decide +kernel
theorem subd14_1_6 : subd14_1 [-4, 1] = true := by decide +kernel
theorem subd14_1_7 : subd14_1 [-4, 2] = true := by decide +kernel
theorem subd14_1_8 : subd14_1 [-4, 3] = true := by decide +kernel
theorem subd14_1_9 : subd14_1 [-4, 4] = true := by decide +kernel
theorem subd14_1_10 : subd14_1 [-3, -5] = true := by decide +kernel
theorem subd14_1_11 : subd14_1 [-3, -4] = true := by decide +kernel
theorem subd14_1_12 : subd14_1 [-3, -3] = true := by decide +kernel
theorem subd14_1_13 : subd14_1 [-3, -2] = true := by decide +kernel
theorem subd14_1_14 : subd14_1 [-3, -1] = true := by decide +kernel
theorem subd14_1_15 : subd14_1 [-3, 0] = true := by decide +kernel
theorem subd14_1_16 : subd14_1 [-3, 1] = true := by decide +kernel
theorem subd14_1_17 : subd14_1 [-3, 2] = true := by decide +kernel
theorem subd14_1_18 : subd14_1 [-3, 3] = true := by decide +kernel
theorem subd14_1_19 : subd14_1 [-3, 4] = true := by decide +kernel
theorem subd14_1_20 : subd14_1 [-3, 5] = true := by decide +kernel
theorem subd14_1_21 : subd14_1 [-2, -6] = true := by decide +kernel
theorem subd14_1_22 : subd14_1 [-2, -5] = true := by decide +kernel
theorem subd14_1_23 : subd14_1 [-2, -4] = true := by decide +kernel
theorem subd14_1_24 : subd14_1 [-2, -3] = true := by decide +kernel
theorem subd14_1_25 : subd14_1 [-2, -2] = true := by decide +kernel
theorem subd14_1_26 : subd14_1 [-2, -1] = true := by decide +kernel
theorem subd14_1_27 : subd14_1 [-2, 0] = true := by decide +kernel
theorem subd14_1_28 : subd14_1 [-2, 1] = true := by decide +kernel
theorem subd14_1_29 : subd14_1 [-2, 2] = true := by decide +kernel
theorem subd14_1_30 : subd14_1 [-2, 3] = true := by decide +kernel
theorem subd14_1_31 : subd14_1 [-2, 4] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_cons.2 ⟨subd14_1_5, List.forall_mem_cons.2 ⟨subd14_1_6, List.forall_mem_cons.2 ⟨subd14_1_7, List.forall_mem_cons.2 ⟨subd14_1_8, List.forall_mem_cons.2 ⟨subd14_1_9, List.forall_mem_cons.2 ⟨subd14_1_10, List.forall_mem_cons.2 ⟨subd14_1_11, List.forall_mem_cons.2 ⟨subd14_1_12, List.forall_mem_cons.2 ⟨subd14_1_13, List.forall_mem_cons.2 ⟨subd14_1_14, List.forall_mem_cons.2 ⟨subd14_1_15, List.forall_mem_cons.2 ⟨subd14_1_16, List.forall_mem_cons.2 ⟨subd14_1_17, List.forall_mem_cons.2 ⟨subd14_1_18, List.forall_mem_cons.2 ⟨subd14_1_19, List.forall_mem_cons.2 ⟨subd14_1_20, List.forall_mem_cons.2 ⟨subd14_1_21, List.forall_mem_cons.2 ⟨subd14_1_22, List.forall_mem_cons.2 ⟨subd14_1_23, List.forall_mem_cons.2 ⟨subd14_1_24, List.forall_mem_cons.2 ⟨subd14_1_25, List.forall_mem_cons.2 ⟨subd14_1_26, List.forall_mem_cons.2 ⟨subd14_1_27, List.forall_mem_cons.2 ⟨subd14_1_28, List.forall_mem_cons.2 ⟨subd14_1_29, List.forall_mem_cons.2 ⟨subd14_1_30, List.forall_mem_cons.2 ⟨subd14_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
