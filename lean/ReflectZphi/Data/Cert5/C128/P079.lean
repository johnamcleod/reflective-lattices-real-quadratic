import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_7_32 : subd10_7 [-1, 4] = true := by decide +kernel
theorem subd10_7_33 : subd10_7 [-1, 5] = true := by decide +kernel
theorem subd10_7_34 : subd10_7 [0, -6] = true := by decide +kernel
theorem subd10_7_35 : subd10_7 [0, -5] = true := by decide +kernel
theorem subd10_7_36 : subd10_7 [0, -4] = true := by decide +kernel
theorem subd10_7_37 : subd10_7 [0, -3] = true := by decide +kernel
theorem subd10_7_38 : subd10_7 [0, -2] = true := by decide +kernel
theorem subd10_7_39 : subd10_7 [0, -1] = true := by decide +kernel
theorem subd10_7_40 : subd10_7 [0, 0] = true := by decide +kernel
theorem subd10_7_41 : subd10_7 [0, 1] = true := by decide +kernel
theorem subd10_7_42 : subd10_7 [0, 2] = true := by decide +kernel
theorem subd10_7_43 : subd10_7 [0, 3] = true := by decide +kernel
theorem subd10_7_44 : subd10_7 [0, 4] = true := by decide +kernel
theorem subd10_7_45 : subd10_7 [0, 5] = true := by decide +kernel
theorem subd10_7_46 : subd10_7 [1, -6] = true := by decide +kernel
theorem subd10_7_47 : subd10_7 [1, -5] = true := by decide +kernel
theorem subd10_7_48 : subd10_7 [1, -4] = true := by decide +kernel
theorem subd10_7_49 : subd10_7 [1, -3] = true := by decide +kernel
theorem subd10_7_50 : subd10_7 [1, -2] = true := by decide +kernel
theorem subd10_7_51 : subd10_7 [1, -1] = true := by decide +kernel
theorem subd10_7_52 : subd10_7 [1, 0] = true := by decide +kernel
theorem subd10_7_53 : subd10_7 [1, 1] = true := by decide +kernel
theorem subd10_7_54 : subd10_7 [1, 2] = true := by decide +kernel
theorem subd10_7_55 : subd10_7 [1, 3] = true := by decide +kernel
theorem subd10_7_56 : subd10_7 [1, 4] = true := by decide +kernel
theorem subd10_7_57 : subd10_7 [1, 5] = true := by decide +kernel
theorem subd10_7_58 : subd10_7 [2, -6] = true := by decide +kernel
theorem subd10_7_59 : subd10_7 [2, -5] = true := by decide +kernel
theorem subd10_7_60 : subd10_7 [2, -4] = true := by decide +kernel
theorem subd10_7_61 : subd10_7 [2, -3] = true := by decide +kernel
theorem subd10_7_62 : subd10_7 [2, -2] = true := by decide +kernel
theorem subd10_7_63 : subd10_7 [2, -1] = true := by decide +kernel
theorem sbd10_7_1 : ∀ q ∈ blkd10_7_1, subd10_7 q = true := by
  unfold blkd10_7_1
  exact List.forall_mem_cons.2 ⟨subd10_7_32, List.forall_mem_cons.2 ⟨subd10_7_33, List.forall_mem_cons.2 ⟨subd10_7_34, List.forall_mem_cons.2 ⟨subd10_7_35, List.forall_mem_cons.2 ⟨subd10_7_36, List.forall_mem_cons.2 ⟨subd10_7_37, List.forall_mem_cons.2 ⟨subd10_7_38, List.forall_mem_cons.2 ⟨subd10_7_39, List.forall_mem_cons.2 ⟨subd10_7_40, List.forall_mem_cons.2 ⟨subd10_7_41, List.forall_mem_cons.2 ⟨subd10_7_42, List.forall_mem_cons.2 ⟨subd10_7_43, List.forall_mem_cons.2 ⟨subd10_7_44, List.forall_mem_cons.2 ⟨subd10_7_45, List.forall_mem_cons.2 ⟨subd10_7_46, List.forall_mem_cons.2 ⟨subd10_7_47, List.forall_mem_cons.2 ⟨subd10_7_48, List.forall_mem_cons.2 ⟨subd10_7_49, List.forall_mem_cons.2 ⟨subd10_7_50, List.forall_mem_cons.2 ⟨subd10_7_51, List.forall_mem_cons.2 ⟨subd10_7_52, List.forall_mem_cons.2 ⟨subd10_7_53, List.forall_mem_cons.2 ⟨subd10_7_54, List.forall_mem_cons.2 ⟨subd10_7_55, List.forall_mem_cons.2 ⟨subd10_7_56, List.forall_mem_cons.2 ⟨subd10_7_57, List.forall_mem_cons.2 ⟨subd10_7_58, List.forall_mem_cons.2 ⟨subd10_7_59, List.forall_mem_cons.2 ⟨subd10_7_60, List.forall_mem_cons.2 ⟨subd10_7_61, List.forall_mem_cons.2 ⟨subd10_7_62, List.forall_mem_cons.2 ⟨subd10_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_7_64 : subd10_7 [2, 0] = true := by decide +kernel
theorem subd10_7_65 : subd10_7 [2, 1] = true := by decide +kernel
theorem subd10_7_66 : subd10_7 [2, 2] = true := by decide +kernel
theorem subd10_7_67 : subd10_7 [2, 3] = true := by decide +kernel
theorem subd10_7_68 : subd10_7 [2, 4] = true := by decide +kernel
theorem subd10_7_69 : subd10_7 [3, -6] = true := by decide +kernel
theorem subd10_7_70 : subd10_7 [3, -5] = true := by decide +kernel
theorem subd10_7_71 : subd10_7 [3, -4] = true := by decide +kernel
theorem subd10_7_72 : subd10_7 [3, -3] = true := by decide +kernel
theorem subd10_7_73 : subd10_7 [3, -2] = true := by decide +kernel
theorem subd10_7_74 : subd10_7 [3, -1] = true := by decide +kernel
theorem subd10_7_75 : subd10_7 [3, 0] = true := by decide +kernel
theorem subd10_7_76 : subd10_7 [3, 1] = true := by decide +kernel
theorem subd10_7_77 : subd10_7 [3, 2] = true := by decide +kernel
theorem subd10_7_78 : subd10_7 [3, 3] = true := by decide +kernel
theorem subd10_7_79 : subd10_7 [4] = true := by decide +kernel
theorem sbd10_7_2 : ∀ q ∈ blkd10_7_2, subd10_7 q = true := by
  unfold blkd10_7_2
  exact List.forall_mem_cons.2 ⟨subd10_7_64, List.forall_mem_cons.2 ⟨subd10_7_65, List.forall_mem_cons.2 ⟨subd10_7_66, List.forall_mem_cons.2 ⟨subd10_7_67, List.forall_mem_cons.2 ⟨subd10_7_68, List.forall_mem_cons.2 ⟨subd10_7_69, List.forall_mem_cons.2 ⟨subd10_7_70, List.forall_mem_cons.2 ⟨subd10_7_71, List.forall_mem_cons.2 ⟨subd10_7_72, List.forall_mem_cons.2 ⟨subd10_7_73, List.forall_mem_cons.2 ⟨subd10_7_74, List.forall_mem_cons.2 ⟨subd10_7_75, List.forall_mem_cons.2 ⟨subd10_7_76, List.forall_mem_cons.2 ⟨subd10_7_77, List.forall_mem_cons.2 ⟨subd10_7_78, List.forall_mem_cons.2 ⟨subd10_7_79, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem subd11_1_1 : subd11_1 [-2, -4] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [1, 3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [2, 2] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
