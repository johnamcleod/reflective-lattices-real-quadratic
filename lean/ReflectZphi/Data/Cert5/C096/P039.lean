import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_0 : subd9_4 [-4] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [-3, -3] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [-3, -2] = true := by decide +kernel
theorem subd9_4_3 : subd9_4 [-3, -1] = true := by decide +kernel
theorem subd9_4_4 : subd9_4 [-3, 0] = true := by decide +kernel
theorem subd9_4_5 : subd9_4 [-3, 1] = true := by decide +kernel
theorem subd9_4_6 : subd9_4 [-3, 2] = true := by decide +kernel
theorem subd9_4_7 : subd9_4 [-3, 3] = true := by decide +kernel
theorem subd9_4_8 : subd9_4 [-3, 4] = true := by decide +kernel
theorem subd9_4_9 : subd9_4 [-2, -4] = true := by decide +kernel
theorem subd9_4_10 : subd9_4 [-2, -3] = true := by decide +kernel
theorem subd9_4_11 : subd9_4 [-2, -2] = true := by decide +kernel
theorem subd9_4_12 : subd9_4 [-2, -1] = true := by decide +kernel
theorem subd9_4_13 : subd9_4 [-2, 0] = true := by decide +kernel
theorem subd9_4_14 : subd9_4 [-2, 1] = true := by decide +kernel
theorem subd9_4_15 : subd9_4 [-2, 2] = true := by decide +kernel
theorem subd9_4_16 : subd9_4 [-2, 3] = true := by decide +kernel
theorem subd9_4_17 : subd9_4 [-2, 4] = true := by decide +kernel
theorem subd9_4_18 : subd9_4 [-2, 5] = true := by decide +kernel
theorem subd9_4_19 : subd9_4 [-1, -5] = true := by decide +kernel
theorem subd9_4_20 : subd9_4 [-1, -4] = true := by decide +kernel
theorem subd9_4_21 : subd9_4 [-1, -3] = true := by decide +kernel
theorem subd9_4_22 : subd9_4 [-1, -2] = true := by decide +kernel
theorem subd9_4_23 : subd9_4 [-1, -1] = true := by decide +kernel
theorem subd9_4_24 : subd9_4 [-1, 0] = true := by decide +kernel
theorem subd9_4_25 : subd9_4 [-1, 1] = true := by decide +kernel
theorem subd9_4_26 : subd9_4 [-1, 2] = true := by decide +kernel
theorem subd9_4_27 : subd9_4 [-1, 3] = true := by decide +kernel
theorem subd9_4_28 : subd9_4 [-1, 4] = true := by decide +kernel
theorem subd9_4_29 : subd9_4 [-1, 5] = true := by decide +kernel
theorem subd9_4_30 : subd9_4 [0, -5] = true := by decide +kernel
theorem subd9_4_31 : subd9_4 [0, -4] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_cons.2 ⟨subd9_4_3, List.forall_mem_cons.2 ⟨subd9_4_4, List.forall_mem_cons.2 ⟨subd9_4_5, List.forall_mem_cons.2 ⟨subd9_4_6, List.forall_mem_cons.2 ⟨subd9_4_7, List.forall_mem_cons.2 ⟨subd9_4_8, List.forall_mem_cons.2 ⟨subd9_4_9, List.forall_mem_cons.2 ⟨subd9_4_10, List.forall_mem_cons.2 ⟨subd9_4_11, List.forall_mem_cons.2 ⟨subd9_4_12, List.forall_mem_cons.2 ⟨subd9_4_13, List.forall_mem_cons.2 ⟨subd9_4_14, List.forall_mem_cons.2 ⟨subd9_4_15, List.forall_mem_cons.2 ⟨subd9_4_16, List.forall_mem_cons.2 ⟨subd9_4_17, List.forall_mem_cons.2 ⟨subd9_4_18, List.forall_mem_cons.2 ⟨subd9_4_19, List.forall_mem_cons.2 ⟨subd9_4_20, List.forall_mem_cons.2 ⟨subd9_4_21, List.forall_mem_cons.2 ⟨subd9_4_22, List.forall_mem_cons.2 ⟨subd9_4_23, List.forall_mem_cons.2 ⟨subd9_4_24, List.forall_mem_cons.2 ⟨subd9_4_25, List.forall_mem_cons.2 ⟨subd9_4_26, List.forall_mem_cons.2 ⟨subd9_4_27, List.forall_mem_cons.2 ⟨subd9_4_28, List.forall_mem_cons.2 ⟨subd9_4_29, List.forall_mem_cons.2 ⟨subd9_4_30, List.forall_mem_cons.2 ⟨subd9_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_32 : subd9_4 [0, -3] = true := by decide +kernel
theorem subd9_4_33 : subd9_4 [0, -2] = true := by decide +kernel
theorem subd9_4_34 : subd9_4 [0, -1] = true := by decide +kernel
theorem subd9_4_35 : subd9_4 [0, 0] = true := by decide +kernel
theorem subd9_4_36 : subd9_4 [0, 1] = true := by decide +kernel
theorem subd9_4_37 : subd9_4 [0, 2] = true := by decide +kernel
theorem subd9_4_38 : subd9_4 [0, 3] = true := by decide +kernel
theorem subd9_4_39 : subd9_4 [0, 4] = true := by decide +kernel
theorem subd9_4_40 : subd9_4 [1, -6] = true := by decide +kernel
theorem subd9_4_41 : subd9_4 [1, -5] = true := by decide +kernel
theorem subd9_4_42 : subd9_4 [1, -4] = true := by decide +kernel
theorem subd9_4_43 : subd9_4 [1, -3] = true := by decide +kernel
theorem subd9_4_44 : subd9_4 [1, -2] = true := by decide +kernel
theorem subd9_4_45 : subd9_4 [1, -1] = true := by decide +kernel
theorem subd9_4_46 : subd9_4 [1, 0] = true := by decide +kernel
theorem subd9_4_47 : subd9_4 [1, 1] = true := by decide +kernel
theorem subd9_4_48 : subd9_4 [1, 2] = true := by decide +kernel
theorem subd9_4_49 : subd9_4 [1, 3] = true := by decide +kernel
theorem subd9_4_50 : subd9_4 [1, 4] = true := by decide +kernel
theorem subd9_4_51 : subd9_4 [2, -6] = true := by decide +kernel
theorem subd9_4_52 : subd9_4 [2, -5] = true := by decide +kernel
theorem subd9_4_53 : subd9_4 [2, -4] = true := by decide +kernel
theorem subd9_4_54 : subd9_4 [2, -3] = true := by decide +kernel
theorem subd9_4_55 : subd9_4 [2, -2] = true := by decide +kernel
theorem subd9_4_56 : subd9_4 [2, -1] = true := by decide +kernel
theorem subd9_4_57 : subd9_4 [2, 0] = true := by decide +kernel
theorem subd9_4_58 : subd9_4 [2, 1] = true := by decide +kernel
theorem subd9_4_59 : subd9_4 [2, 2] = true := by decide +kernel
theorem subd9_4_60 : subd9_4 [2, 3] = true := by decide +kernel
theorem subd9_4_61 : subd9_4 [3, -5] = true := by decide +kernel
theorem subd9_4_62 : subd9_4 [3, -4] = true := by decide +kernel
theorem subd9_4_63 : subd9_4 [3, -3] = true := by decide +kernel
theorem sbd9_4_1 : ∀ q ∈ blkd9_4_1, subd9_4 q = true := by
  unfold blkd9_4_1
  exact List.forall_mem_cons.2 ⟨subd9_4_32, List.forall_mem_cons.2 ⟨subd9_4_33, List.forall_mem_cons.2 ⟨subd9_4_34, List.forall_mem_cons.2 ⟨subd9_4_35, List.forall_mem_cons.2 ⟨subd9_4_36, List.forall_mem_cons.2 ⟨subd9_4_37, List.forall_mem_cons.2 ⟨subd9_4_38, List.forall_mem_cons.2 ⟨subd9_4_39, List.forall_mem_cons.2 ⟨subd9_4_40, List.forall_mem_cons.2 ⟨subd9_4_41, List.forall_mem_cons.2 ⟨subd9_4_42, List.forall_mem_cons.2 ⟨subd9_4_43, List.forall_mem_cons.2 ⟨subd9_4_44, List.forall_mem_cons.2 ⟨subd9_4_45, List.forall_mem_cons.2 ⟨subd9_4_46, List.forall_mem_cons.2 ⟨subd9_4_47, List.forall_mem_cons.2 ⟨subd9_4_48, List.forall_mem_cons.2 ⟨subd9_4_49, List.forall_mem_cons.2 ⟨subd9_4_50, List.forall_mem_cons.2 ⟨subd9_4_51, List.forall_mem_cons.2 ⟨subd9_4_52, List.forall_mem_cons.2 ⟨subd9_4_53, List.forall_mem_cons.2 ⟨subd9_4_54, List.forall_mem_cons.2 ⟨subd9_4_55, List.forall_mem_cons.2 ⟨subd9_4_56, List.forall_mem_cons.2 ⟨subd9_4_57, List.forall_mem_cons.2 ⟨subd9_4_58, List.forall_mem_cons.2 ⟨subd9_4_59, List.forall_mem_cons.2 ⟨subd9_4_60, List.forall_mem_cons.2 ⟨subd9_4_61, List.forall_mem_cons.2 ⟨subd9_4_62, List.forall_mem_cons.2 ⟨subd9_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_64 : subd9_4 [3, -2] = true := by decide +kernel
theorem subd9_4_65 : subd9_4 [3, -1] = true := by decide +kernel
theorem subd9_4_66 : subd9_4 [3, 0] = true := by decide +kernel
theorem subd9_4_67 : subd9_4 [3, 1] = true := by decide +kernel
theorem subd9_4_68 : subd9_4 [3, 2] = true := by decide +kernel
theorem subd9_4_69 : subd9_4 [4] = true := by decide +kernel
theorem sbd9_4_2 : ∀ q ∈ blkd9_4_2, subd9_4 q = true := by
  unfold blkd9_4_2
  exact List.forall_mem_cons.2 ⟨subd9_4_64, List.forall_mem_cons.2 ⟨subd9_4_65, List.forall_mem_cons.2 ⟨subd9_4_66, List.forall_mem_cons.2 ⟨subd9_4_67, List.forall_mem_cons.2 ⟨subd9_4_68, List.forall_mem_cons.2 ⟨subd9_4_69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
